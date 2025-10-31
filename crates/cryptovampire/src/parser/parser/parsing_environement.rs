use std::borrow::Borrow;
use std::collections::VecDeque;
use std::ops::Deref;
use std::sync::Arc;

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use log::trace;
use utils::maybe_owned::MOw;
use utils::string_ref::StrRef;
use utils::utils::MaybeInvalid;
use utils::{implderef, implvec};

use crate::container::ScopedContainer;
use crate::environement::traits::{KnowsRealm, Realm};
use crate::error::{CVContext, LocateHelper};
use crate::formula::function::Function;
use crate::formula::function::inner::evaluate::Evaluator;
use crate::formula::function::name_caster_collection::{DEFAULT_NAME_CASTER, NameCasterCollection};
use crate::formula::sort::Sort;
use crate::parser::Pstr;
use crate::parser::ast::{self, ASTList};
use crate::parser::error::ParsingError;
use crate::parser::location::ASTLocation;
use crate::parser::parser::{
    parse_assert_with_bvars, parse_asserts_crypto, parse_asserts_with_bvars, parse_cells,
    parse_orders_with_bvars, parse_steps,
};
use crate::problem::cell::MemoryCell;
use crate::problem::problem::{Problem, ProblemBuilder};
use crate::problem::protocol::Protocol;
use crate::problem::step::Step;

#[derive(Hash, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Macro<'bump, 'str, S> {
    /// The sort of the arguments
    pub args: Arc<[Sort<'bump>]>,
    /// Their name
    pub args_name: Arc<[S]>,
    /// The body
    pub content: ast::Term<'str, S>,
}

pub use cache::{CellCache, FunctionCache, StepCache};

use super::parsable_trait::{
    FALSE_CACHE, FALSE_TA_CACHE, NOT_CACHE, NOT_TA_CACHE, TRUE_CACHE, TRUE_TA_CACHE,
};
use super::{declare_sorts, fetch_all};

mod cache;

#[derive(Debug)]
pub struct Environement<'bump, 'str, S> {
    /// the main memory
    pub container: &'bump ScopedContainer<'bump>,

    /// some hash map to quickly turn [String] likes into [Sort] or [Function] during parsing.
    ///
    /// This is basically the non-variable bounded names
    ///
    /// This one is for [Sort]
    pub sort_hash: HashMap<String, Sort<'bump>>,
    /// That one for [Function]s
    // pub function_hash: HashMap<String, Function<'bump>>,
    pub name_caster_collection: NameCasterCollection<'bump>,
    pub evaluator: Evaluator<'bump>,

    /// For [Macro]s
    pub macro_hash: HashMap<String, Macro<'bump, 'str, S>>,
    /// # Macro look up table
    // pub step_lut_to_parse: HashMap<&'str str, ast::Step<'str>>,
    pub functions: HashMap<String, FunctionCache<'str, 'bump, S>>,

    pub used_name: HashSet<String>,
    pub allow_shadowing: bool,
}

impl<'bump, 'str, S> MaybeInvalid for Environement<'bump, 'str, S> {
    fn is_valid(&self) -> bool {
        let Environement {
            name_caster_collection: _,
            container: _,
            sort_hash: _,
            macro_hash: _,
            evaluator: _,
            functions,
            used_name: _,
            allow_shadowing: _,
        } = self;

        functions.values().all(|v| match v {
            FunctionCache::Function(function) => function.is_valid(),
            FunctionCache::Step(StepCache { function, step, .. }) => {
                function.is_valid() && step.is_valid()
            }
            FunctionCache::MemoryCell(CellCache { cell, function, .. }) => {
                function.is_valid() && cell.is_valid()
            }
        })
    }
}

impl<'bump, 'str, S> Environement<'bump, 'str, S> {
    pub fn new(
        container: &'bump ScopedContainer<'bump>,
        sort_hash: implvec!(Sort<'bump>),
        function_hash: implvec!(Function<'bump>),
        extra_names: implvec!(String),
        allow_shadowing: bool,
    ) -> Self {
        let sort_hash = sort_hash
            .into_iter()
            .map(|s| (s.name().to_string(), s))
            .collect();
        let function_hash: HashMap<_, _> = function_hash
            .into_iter()
            .map(|f| (f.name().into(), cache::FunctionCache::Function(f)))
            .collect();

        let names = extra_names.into_iter().collect();

        Self {
            name_caster_collection: DEFAULT_NAME_CASTER.clone(),
            container,
            sort_hash,
            evaluator: Default::default(),
            // those start empty
            macro_hash: Default::default(),
            functions: function_hash,
            used_name: names,
            allow_shadowing,
        }
    }

    pub fn contains_name(&self, name: &str) -> bool {
        self.functions.contains_key(name) || self.used_name.contains(name)
    }

    pub fn contains_name_with_var<'b>(&self, name: &'b str, vars: implvec!(&'b str)) -> bool {
        self.contains_name(name) || vars.into_iter().contains(&name)
    }

    pub fn container_macro_name(&self, name: &str) -> bool {
        self.macro_hash.contains_key(name) || self.used_name.contains(&format!("{name}!"))
    }

    fn get_steps(&self) -> impl Iterator<Item = Step<'bump>> + '_ {
        self.functions
            .values()
            .filter_map(|f| f.as_step())
            .map(|StepCache { step, .. }| *step)
    }

    fn get_cells(&self) -> impl Iterator<Item = MemoryCell<'bump>> + '_ {
        self.functions
            .values()
            .filter_map(|f| f.as_memory_cell())
            .map(|CellCache { cell, .. }| *cell)
    }

    fn get_functions(&self) -> impl Iterator<Item = Function<'bump>> + '_ {
        self.functions
            .values()
            // .filter_map(|f| f.as_function())
            .map(|f| f.get_function())
    }

    fn get_sorts(&self) -> impl Iterator<Item = Sort<'bump>> + '_ {
        self.sort_hash.values().cloned()
    }

    pub fn find_function<'b>(
        &'b self,
        span: &ASTLocation<'str>,
        name: &str,
    ) -> crate::Result<&'b FunctionCache<'str, 'bump, S>> {
        get_function(self, span, name)
    }

    pub fn find_sort<'b>(
        &'b self,
        span: &ASTLocation<'str>,
        name: &str,
    ) -> crate::Result<Sort<'bump>> {
        get_sort(self, span, name)
    }

    /// consume `self` to build a [Problem]
    pub fn into_problem<'b>(
        self,
        pbl_builder: &'b mut ProblemBuilder<'bump>,
    ) -> &'b mut ProblemBuilder<'bump> {
        pbl_builder
            .functions(self.get_functions().collect())
            .sorts(self.get_sorts().collect())
            .evaluator(Arc::new(self.evaluator.clone()))
            .name_caster(Arc::new(self.name_caster_collection.clone()))
    }

    pub fn allow_shadowing(&self) -> bool {
        self.allow_shadowing
    }
}

/// Find the [Sort] in already declared in [Environement::sort_hash]
pub fn get_sort<'str, 'bump, S, L: LocateHelper>(
    env: &Environement<'bump, 'str, S>,
    span: &L,
    str: implderef!(str),
) -> crate::Result<Sort<'bump>> {
    env.sort_hash
        .get(Deref::deref(&str))
        .ok_or_else(|| ParsingError::undefined_sort(&str))
        .with_pre_location(span, &str.deref())
        .copied()
}

/// Find the [Function] in already declared in [Environement::functions]
pub fn get_function<'b, 'a, 'bump, L: LocateHelper, S>(
    env: &'b Environement<'bump, 'a, S>,
    span: &L,
    str: implderef!(str),
) -> crate::Result<&'b FunctionCache<'a, 'bump, S>> {
    env.functions
        .get(Deref::deref(&str))
        .ok_or_else(|| ParsingError::undefined_function(&str))
        .with_pre_location(span, &str.deref())
    // .map(|s| *s)
}

pub fn get_function_mow<'b, 'a, 'bump, L: LocateHelper, S>(
    content: &S,
    state: &impl KnowsRealm,
    env: &'b Environement<'bump, 'a, S>,
    span: &L,
) -> crate::Result<MOw<'b, FunctionCache<'a, 'bump, S>>>
where
    S: Borrow<str>,
{
    match content.borrow() {
        "true" | "True" => Ok(match state.get_realm() {
            Realm::Symbolic => TRUE_TA_CACHE(),
            Realm::Evaluated => TRUE_CACHE(),
        }),
        "false" | "False" => Ok(match state.get_realm() {
            Realm::Symbolic => FALSE_TA_CACHE(),
            Realm::Evaluated => FALSE_CACHE(),
        }),
        "not" => Ok(match state.get_realm() {
            Realm::Symbolic => NOT_TA_CACHE(),
            Realm::Evaluated => NOT_CACHE(),
        }),
        _ => get_function(env, span, content.borrow()).map(MOw::Borrowed),
    }
}

impl<'a, 'bump, S> KnowsRealm for Environement<'bump, 'a, S> {
    fn get_realm(&self) -> Realm {
        Realm::Evaluated
    }
}

/// Create a problem from a [ast::ASTList]
pub fn parse_pbl_from_ast<'bump, 'str, S>(
    container: &'bump ScopedContainer<'bump>,
    sort_hash: implvec!(Sort<'bump>),
    function_hash: implvec!(Function<'bump>),
    extra_names: implvec!(String),
    ast: ASTList<'str, S>,
    ignore_lemmas: bool,
    allow_shadowing: bool,
) -> crate::Result<Problem<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    trace!("[P] parsing from ast...");
    let mut pbl_builder = ProblemBuilder::default();
    pbl_builder.container(container);

    let env = Environement::new(
        container,
        sort_hash,
        function_hash,
        extra_names,
        allow_shadowing,
    );
    prbl_from_ast(env, &ast, pbl_builder, ignore_lemmas, container)
}

fn prbl_from_ast<'a, 'bump, S>(
    mut env: Environement<'bump, 'a, S>,
    ast: &'a ASTList<'a, S>,
    mut pbl_builder: ProblemBuilder<'bump>,
    ignore_lemmas: bool,
    container: &'bump ScopedContainer<'bump>,
) -> crate::Result<Problem<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    trace!("[P] \t- sorts...");
    declare_sorts::<S>(&mut env, ast)?;
    //             ^^^^^^^^^ why ???

    let mut assertions = Vec::new();
    let mut lemmas = Vec::new();
    let mut orders = Vec::new();
    let mut asserts_crypto = Vec::new();

    trace!("[P] \t- fetch all...");
    let query = fetch_all::<S>(
        //                 ^^^^^^^^^ same ???
        &mut env,
        ast,
        &mut assertions,
        &mut lemmas,
        &mut orders,
        &mut asserts_crypto,
    )?;
    trace!("[P] \t[DONE]");

    trace!("[P] \t- parse steps...");
    parse_steps::<S>(&env, env.functions.values().filter_map(|f| f.as_step()))?;
    trace!("[P] \t[DONE]");
    trace!("[P] \t- parse cells...");
    parse_cells::<S>(
        &env,
        env.functions.values().filter_map(|f| f.as_memory_cell()),
    )?;
    trace!("[P] \t[DONE]");
    assert!(env.is_valid());

    trace!("[P] \t- parse assertions...");
    let mut bvars = Vec::new();
    pbl_builder
        .assertions(parse_asserts_with_bvars::<Vec<_>, S>(
            &env, assertions, &mut bvars,
        )?)
        .query(parse_assert_with_bvars::<S>(&env, query, &mut bvars)?)
        .crypto_assertions(parse_asserts_crypto::<S>(&env, asserts_crypto)?);
    if !ignore_lemmas {
        pbl_builder.lemmas(parse_asserts_with_bvars::<VecDeque<_>, S>(
            &env, lemmas, &mut bvars,
        )?);
    }
    let orders: Vec<_> = parse_orders_with_bvars::<Vec<_>, S>(&env, orders, &mut bvars)?;
    let _ = bvars;
    trace!("[P] \t[DONE]");

    trace!("[P] \t- into problem...");
    pbl_builder.protocol(Protocol::new(env.get_steps(), env.get_cells(), orders));
    trace!("[P] \t[DONE]");

    trace!("[P] \t-gathering quantifiers");
    {
        let quantifier = container.get_functions_vec_filtered(|f| f.as_quantifer().is_some());
        env.functions.extend(
            quantifier
                .into_iter()
                .map(|f| (f.name().to_string(), f.into())),
        );
    }

    if cfg!(debug_assertions) {
        for f in env.get_functions() {
            trace!("{} is valid", f.name())
        }
    }

    trace!("[P] \tparsing done");
    env.into_problem(&mut pbl_builder);

    Ok(pbl_builder.build()?)
}
