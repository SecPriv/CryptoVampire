use std::{collections::VecDeque, ops::Deref, sync::Arc};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use log::trace;

use crate::{
    err_at,
    parser::{
        ast::{self, ASTList},
        parser::{
            parse_assert_with_bvars, parse_asserts_crypto, parse_asserts_with_bvars, parse_cells,
            parse_orders_with_bvars, parse_steps,
        },
        Location, MResult, Pstr,
    },
};
use cryptovampire_lib::{
    container::ScopedContainer,
    environement::traits::{KnowsRealm, Realm},
    formula::{
        function::{
            inner::evaluate::Evaluator,
            name_caster_collection::{NameCasterCollection, DEFAULT_NAME_CASTER},
            Function,
        },
        sort::Sort,
    },
    problem::{
        cell::MemoryCell,
        problem::{Problem, ProblemBuilder},
        protocol::Protocol,
        step::Step,
    },
};
use utils::{implderef, implvec, string_ref::StrRef, traits::NicerError, utils::MaybeInvalid};

#[derive(Hash, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Macro<'bump, 'a, S> {
    // name: &'a str,
    pub args: Arc<[Sort<'bump>]>,
    pub args_name: Arc<[S]>,
    pub content: ast::Term<'a, S>,
}

pub use cache::{CellCache, FunctionCache, StepCache};

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
}

impl<'bump, 'a, S> MaybeInvalid for Environement<'bump, 'a, S> {
    fn is_valid(&self) -> bool {
        let Environement {
            name_caster_collection: _,
            container: _,
            sort_hash: _,
            macro_hash: _,
            evaluator: _,
            functions,
            used_name: _,
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

impl<'bump, 'str, S> Environement<'bump, 'str, S>
where
    'str: 'str,
{
    pub fn shorten_life<'a>(self) -> Environement<'bump, 'a, S>
    where
        'str: 'a,
    {
        self
    }

    pub fn new(
        container: &'bump ScopedContainer<'bump>,
        sort_hash: implvec!(Sort<'bump>),
        function_hash: implvec!(Function<'bump>),
        extra_names: implvec!(String),
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
        span: Location<'str>,
        name: &str,
    ) -> MResult<&'b FunctionCache<'str, 'bump, S>> {
        get_function(self, span, name)
    }

    pub fn find_sort<'b>(&'b self, span: Location<'str>, name: &str) -> MResult<Sort<'bump>> {
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
}

/// Find the [Sort] in already declared in [Environement::sort_hash]
pub fn get_sort<'a, 'bump, S>(
    env: &Environement<'bump, 'a, S>,
    span: Location<'a>,
    str: implderef!(str),
) -> MResult<Sort<'bump>> {
    env.sort_hash
        .get(Deref::deref(&str))
        .ok_or_else(|| err_at!(&span, "undefined sort {}", Deref::deref(&str)))
        .map(|s| *s)
}

/// Find the [Function] in already declared in [Environement::functions]
pub fn get_function<'b, 'a, 'bump, S>(
    env: &'b Environement<'bump, 'a, S>,
    span: Location<'a>,
    str: implderef!(str),
) -> MResult<&'b FunctionCache<'a, 'bump, S>> {
    env.functions.get(Deref::deref(&str)).ok_or_else(|| {
        err_at!(
            &span,
            "undefined function {}\nhint: If you looked for a macro, maybe you forgot the '!'",
            Deref::deref(&str)
        )
    })
    // .map(|s| *s)
}

impl<'a, 'bump, S> KnowsRealm for Environement<'bump, 'a, S> {
    fn get_realm(&self) -> Realm {
        Realm::Evaluated
    }
}

pub fn parse_str<'a, 'bump>(
    container: &'bump ScopedContainer<'bump>,
    sort_hash: implvec!(Sort<'bump>),
    function_hash: implvec!(Function<'bump>),
    extra_names: implvec!(String),
    str: &'a str,
    ignore_lemmas: bool,
) -> anyhow::Result<Problem<'bump>> {
    let mut pbl_builder = ProblemBuilder::default();
    pbl_builder.container(container);
    trace!("[P] parsing...");

    let pbl = {
        trace!("[P] \tinto ast...");
        let ast = ASTList::try_from(str).debug_continue()?;
        let env = Environement::new(container, sort_hash, function_hash, extra_names);
        trace!("[P] \t[DONE]");

        prbl_from_ast(
            env.shorten_life(),
            &*&ast,
            pbl_builder,
            ignore_lemmas,
            container,
        )?
    };

    Ok(pbl)
}

// pub fn parse_test<'a, 'bump>(
//     container: &'bump ScopedContainer<'bump>,
//     sort_hash: Vec<Sort<'bump>>,
//     function_hash: Vec<Function<'bump>>,
//     extra_names: Vec<String>,
//     str: &'a str,
//     ignore_lemmas: bool,
// ) -> anyhow::Result<Problem<'bump>> {
//     let mut pbl_builder: ProblemBuilder<'bump> = ProblemBuilder::default();
//     pbl_builder.container(container);

//     let ast = ASTList::try_from(str).debug_continue()?;
//     let env = Environement::new(container, sort_hash, function_hash, extra_names);

//     prbl_from_ast_test(
//         env,
//         &ast,
//         pbl_builder,
//         ignore_lemmas,
//         container,
//     );
//     todo!();

//     // Ok(pbl)
// }

// fn prbl_from_ast_test<'a, 'bump, S>(
//     mut env: Environement<'bump, 'a, S>,
//     ast: &'a ASTList<'a, S>,
//     mut pbl_builder: ProblemBuilder<'bump>,
//     ignore_lemmas: bool,
//     container: &'bump ScopedContainer<'bump>,
// ) -> Result<Problem<'bump>, anyhow::Error>
// where
//     S: From<&'static str>,
// {
//     todo!()
// }

fn prbl_from_ast<'a, 'bump, S>(
    mut env: Environement<'bump, 'a, S>,
    ast: &'a ASTList<'a, S>,
    mut pbl_builder: ProblemBuilder<'bump>,
    ignore_lemmas: bool,
    container: &'bump ScopedContainer<'bump>,
) -> Result<Problem<'bump>, anyhow::Error>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    trace!("[P] \t- sorts...");
    declare_sorts::<S>(&mut env, &ast).debug_continue()?;
    //             ^^^^^^^^^ why ???

    let mut assertions = Vec::new();
    let mut lemmas = Vec::new();
    let mut orders = Vec::new();
    let mut asserts_crypto = Vec::new();

    trace!("[P] \t- fetch all...");
    let query = fetch_all::<S>(
        //                 ^^^^^^^^^ same ???
        &mut env,
        &ast,
        &mut assertions,
        &mut lemmas,
        &mut orders,
        &mut asserts_crypto,
    )
    .debug_continue()?;
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
