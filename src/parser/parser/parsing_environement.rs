use std::ops::Deref;

use hashbrown::HashMap;
use pest::Span;

use crate::{
    container::{allocator::ContainerTools, ScopedContainer},
    environement::traits::KnowsRealm,
    f,
    formula::{
        function::{Function, InnerFunction},
        sort::Sort,
        variable::Variable,
    },
    implderef, implvec,
    parser::{ast, merr, parser::guard::Guard, E},
    problem::{cell::InnerMemoryCell, step::InnerStep},
    utils::utils::MaybeInvalid,
};

use super::guard::{GuardedFunction, GuardedMemoryCell, GuardedStep};

#[derive(Hash, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Macro<'bump, 'a> {
    // name: &'a str,
    pub args: Vec<(&'a str, Variable<'bump>)>,
    pub content: ast::Term<'a>,
}

#[derive(Debug)]
pub struct Environement<'bump, 'str> {
    /// the main memory
    pub container: &'bump ScopedContainer<'bump>,

    /// some hash map to quickly turn [String] likes into [Sort] or [Function] during parsing.
    ///
    /// This is basically the non-variable bounded names
    ///
    /// This one is for [Sort]
    pub sort_hash: HashMap<&'bump str, Sort<'bump>>,
    /// That one for [Function]s
    pub function_hash: HashMap<String, Function<'bump>>,

    /// For [Macro]s
    pub macro_hash: HashMap<&'str str, Macro<'bump, 'str>>,
    /// # Macro look up table
    pub step_lut_to_parse: HashMap<&'str str, ast::Step<'str>>,

    /// List of things to initialize
    ///
    /// Those are recurive structure or immutable structure which cannot be built at once.
    /// Instead we define them incrementally and once the parsing is done, we call [Self::finalize()]
    ///
    /// We use [`Guard<T>`] to ensure only the trait we know won't call the underlying `T` in
    /// that are not initialized yet.
    ///
    /// This one is for [Function]
    pub functions_initialize: HashMap<GuardedFunction<'bump>, Option<InnerFunction<'bump>>>,
    /// For [Step][crate::problem::step::Step]
    pub steps_initialize: HashMap<GuardedStep<'bump>, Option<InnerStep<'bump>>>,
    /// For [MemoryCell][crate::problem::cell::MemoryCell]
    pub cells_initialize: HashMap<GuardedMemoryCell<'bump>, Option<InnerMemoryCell<'bump>>>,
}

impl<'bump, 'a> MaybeInvalid for Environement<'bump, 'a> {
    fn is_valid(&self) -> bool {
        todo!()
    }
}

impl<'bump, 'a> Environement<'bump, 'a> {
    pub fn new(
        container: &'bump ScopedContainer<'bump>,
        sort_hash: implvec!(Sort<'bump>),
        function_hash: implvec!(Function<'bump>),
    ) -> Self {
        let sort_hash = sort_hash.into_iter().map(|s| (s.name(), s)).collect();
        let function_hash = function_hash
            .into_iter()
            .map(|f| (f.name().into(), f))
            .collect();

        Self {
            container,
            sort_hash,
            function_hash,
            /// those start empty
            step_lut_to_parse: Default::default(),
            macro_hash: Default::default(),
            functions_initialize: Default::default(),
            steps_initialize: Default::default(),
            cells_initialize: Default::default(),
        }
    }

    pub fn finalize(&mut self) {
        fn finalize_hash_map<'bump, C, T>(
            _container: &C,
            h: &mut HashMap<Guard<C::R<'bump>>, Option<T>>,
        ) where
            C: ContainerTools<'bump, T>,
        {
            std::mem::take(h)
                .into_iter()
                // This returns shortcuts to `None` if `fun` is `None`
                .try_for_each(|(g, fun)| {
                    fun.map(|fun| unsafe { C::initialize(&g, fun) })
                        .expect("unreachable: all inner should be ready")
                })
                .expect("unreachable: nothing was initialized before") // should never crash
        }

        let Environement {
            functions_initialize,
            steps_initialize,
            cells_initialize,
            ..
        } = self;

        finalize_hash_map(self.container, functions_initialize);
        finalize_hash_map(self.container, steps_initialize);
        finalize_hash_map(self.container, cells_initialize);

        assert!(self.is_valid(), "something went wrong while initializing");
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
pub fn get_function<'a, 'bump>(
    env: &Environement<'bump, 'a>,
    span: Span<'a>,
    str: implderef!(str),
) -> Result<Function<'bump>, E> {
    env.function_hash
        .get(Deref::deref(&str))
        .ok_or_else(|| merr(span, f!("undefined function {}", Deref::deref(&str))))
        .map(|s| *s)
}

impl<'a, 'bump> KnowsRealm for Environement<'bump, 'a> {
    fn get_realm(&self) -> crate::environement::traits::Realm {
        todo!()
    }
}
