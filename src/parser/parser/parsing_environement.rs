use std::{ops::Deref, sync::Arc};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use pest::Span;

use crate::{
    container::ScopedContainer,
    environement::traits::KnowsRealm,
    f,
    formula::{
        function::{
            inner::{
                evaluate::Evaluator,
                term_algebra::name::{NameCasterCollection, DEFAULT_NAME_CASTER},
            },
            Function,
        },
        sort::Sort,
        variable::Variable,
    },
    implderef, implvec,
    parser::{ast, merr, E},
    utils::utils::MaybeInvalid,
};

#[derive(Hash, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Macro<'bump, 'a> {
    // name: &'a str,
    pub args: Arc<[Sort<'bump>]>,
    pub args_name: Arc<[&'a str]>,
    pub content: ast::Term<'a>,
}

pub use cache::FunctionCache;

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
            FunctionCache::Function { function } => function.is_valid(),
            FunctionCache::Step { function, step, .. } => function.is_valid() && step.is_valid(),
            FunctionCache::MemoryCell { cell, function, .. } => {
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
            .map(|f| {
                (
                    f.name().into(),
                    cache::FunctionCache::Function { function: f },
                )
            })
            .collect();

        let names = function_hash
            .keys()
            .cloned()
            .chain(extra_names.into_iter())
            .collect();

        Self {
            name_caster_collection: DEFAULT_NAME_CASTER.clone(),
            container,
            sort_hash,
            evaluator: Default::default(),
            /// those start empty
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
    env.functions
        .get(Deref::deref(&str))
        .ok_or_else(|| merr(span, f!("undefined function {}", Deref::deref(&str))))
    // .map(|s| *s)
}

impl<'a, 'bump> KnowsRealm for Environement<'bump, 'a> {
    fn get_realm(&self) -> crate::environement::traits::Realm {
        todo!()
    }
}
