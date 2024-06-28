use std::{ops::Deref, sync::Arc};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use log::trace;
use pest::Span;

use crate::parser::{
    ast::{self, ASTList},
    merr,
    parser::{
        parse_assert_with_bvars, parse_asserts_crypto, parse_asserts_with_bvars, parse_cells,
        parse_orders_with_bvars, parse_steps,
    },
    E,
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
use utils::{
    f, implderef, implvec,
    {traits::NicerError, utils::MaybeInvalid},
};

#[derive(Hash, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Macro<'bump, 'a> {
    // name: &'a str,
    pub args: Arc<[Sort<'bump>]>,
    pub args_name: Arc<[&'a str]>,
    pub content: ast::Term<'a>,
}

pub use cache::{CellCache, FunctionCache, StepCache};

use super::{declare_sorts, fetch_all};

mod cache;

#[derive(Debug)]
pub struct Environement<'bump, 'str> {
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
    pub macro_hash: HashMap<String, Macro<'bump, 'str>>,
    /// # Macro look up table
    // pub step_lut_to_parse: HashMap<&'str str, ast::Step<'str>>,
    pub functions: HashMap<String, FunctionCache<'str, 'bump>>,

    pub used_name: HashSet<String>,
}

impl<'bump, 'a> MaybeInvalid for Environement<'bump, 'a> {
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

impl<'bump, 'a> Environement<'bump, 'a> {
    pub fn new(
        container: &'bump ScopedContainer<'bump>,
        sort_hash: implvec!(Sort<'bump>),
        function_hash: implvec!(Function<'bump>),
        extra_names: implvec!(String),
    ) -> Self {
        let sort_hash = sort_hash
            .into_iter()
            .map(|s| (s.name().into_string(), s))
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

    // pub fn finalize(&mut self) {
    //     fn finalize_hash_map<'bump, C, T>(
    //         _container: &C,
    //         h: &mut HashMap<Guard<C::R<'bump>>, Option<T>>,
    //     ) where
    //         C: ContainerTools<'bump, T>,
    //     {
    //         std::mem::take(h)
    //             .into_iter()
    //             // This returns shortcuts to `None` if `fun` is `None`
    //             .try_for_each(|(g, fun)| {
    //                 fun.map(|fun| unsafe { C::initialize(&g, fun) })
    //                     .expect("unreachable: all inner should be ready")
    //             })
    //             .expect("unreachable: nothing was initialized before") // should never crash
    //     }

    //     let Environement {
    //         functions_initialize,
    //         steps_initialize,
    //         cells_initialize,
    //         ..
    //     } = self;

    //     finalize_hash_map(self.container, functions_initialize);
    //     finalize_hash_map(self.container, steps_initialize);
    //     finalize_hash_map(self.container, cells_initialize);

    //     assert!(self.is_valid(), "something went wrong while initializing");
    // }

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
        span: Span<'a>,
        name: &str,
    ) -> Result<&'b FunctionCache<'a, 'bump>, E> {
        get_function(self, span, name)
    }

    pub fn find_sort<'b>(&'b self, span: Span<'a>, name: &str) -> Result<Sort<'bump>, E> {
        get_sort(self, span, name)
    }
}

/// Find the [Sort] in already declared in [Environement::sort_hash]
pub fn get_sort<'a, 'bump>(
    env: &Environement<'bump, 'a>,
    span: Span<'a>,
    str: implderef!(str),
) -> Result<Sort<'bump>, E> {
    env.sort_hash
        .get(Deref::deref(&str))
        .ok_or_else(|| merr(span, f!("undefined sort {}", Deref::deref(&str))))
        .map(|s| *s)
}

/// Find the [Function] in already declared in [Environement::sort_function]
pub fn get_function<'b, 'a, 'bump>(
    env: &'b Environement<'bump, 'a>,
    span: Span<'a>,
    str: implderef!(str),
) -> Result<&'b FunctionCache<'a, 'bump>, E> {
    env.functions.get(Deref::deref(&str)).ok_or_else(|| {
        merr(
            span,
            f!(
                "undefined function {}\nhint: If you looked for a macro, maybe you forgot the '!'",
                Deref::deref(&str)
            ),
        )
    })
    // .map(|s| *s)
}

impl<'a, 'bump> KnowsRealm for Environement<'bump, 'a> {
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
) -> Result<Problem<'bump>, E> {
    trace!("[P] parsing...");

    trace!("[P] \tinto ast...");
    let ast: ASTList<'a> = str.try_into().debug_continue()?;
    let mut env = Environement::new(container, sort_hash, function_hash, extra_names);
    trace!("[P] \t[DONE]");

    trace!("[P] \t- sorts...");
    declare_sorts(&mut env, &ast).debug_continue()?;

    let mut assertions = Vec::new();
    let mut lemmas = Vec::new();
    let mut orders = Vec::new();
    let mut asserts_crypto = Vec::new();

    trace!("[P] \t- fetch all...");
    let query = fetch_all(
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
    parse_steps(&env, env.functions.values().filter_map(|f| f.as_step())).debug_continue()?;
    trace!("[P] \t[DONE]");
    trace!("[P] \t- parse cells...");
    parse_cells(
        &env,
        env.functions.values().filter_map(|f| f.as_memory_cell()),
    )
    .debug_continue()?;
    trace!("[P] \t[DONE]");
    assert!(env.is_valid());

    trace!("[P] \t- parse assertions...");
    let mut bvars = Vec::new();
    let assertions: Vec<_> =
        parse_asserts_with_bvars(&env, assertions, &mut bvars).debug_continue()?;
    let lemmas = parse_asserts_with_bvars(&env, lemmas, &mut bvars).debug_continue()?;
    let query = parse_assert_with_bvars(&env, query, &mut bvars).debug_continue()?;
    let orders: Vec<_> = parse_orders_with_bvars(&env, orders, &mut bvars).debug_continue()?;
    let asserts_crypto = parse_asserts_crypto(&env, asserts_crypto).debug_continue()?;
    let _ = bvars;
    trace!("[P] \t[DONE]");

    trace!("[P] \t- into problem...");
    let protocol = Protocol::new(env.get_steps(), env.get_cells(), orders);
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
    // let pbl = Problem {
    //     functions: env.get_functions().collect(),
    //     sorts: env.get_sorts().collect(),
    //     evaluator: Arc::new(env.evaluator.clone()),
    //     name_caster: Arc::new(env.name_caster_collection.clone()),
    //     protocol,
    //     assertions,
    //     lemmas,
    //     query,
    //     container,
    //     crypto_assertions: asserts_crypto,
    //     extra_instances: Default::default(),
    // };

    // Ok(pbl)
    let mut pbl_builder = ProblemBuilder::default();
    pbl_builder
        .functions(env.get_functions().collect())
        .sorts(env.get_sorts().collect())
        .evaluator(Arc::new(env.evaluator.clone()))
        .name_caster(Arc::new(env.name_caster_collection.clone()))
        .protocol(protocol)
        .assertions(assertions)
        // .lemmas(lemmas)
        .query(query)
        .container(container)
        .crypto_assertions(asserts_crypto);

    if !ignore_lemmas {
        pbl_builder.lemmas(lemmas);
    }
    Ok(pbl_builder.build().unwrap())
}
