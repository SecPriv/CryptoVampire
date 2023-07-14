use std::{collections::HashMap, ops::Deref};

use pest::Span;

use self::guard::{GuardedFunction, GuardedMemoryCell, GuardedStep};

use super::{
    ast::{
        extra::{self, AsFunction, SnN},
        ASTList, Declaration, DeclareType, Ident, AST,
    },
    *,
};
use crate::{
    container::Container,
    formula::{
        function::{Function, InnerFunction},
        sort::{InnerSort, Sort},
    },
    implderef, implvec,
    parser::parser::guard::Guard,
    problem::{cell::InnerMemoryCell, step::InnerStep},
    utils::{
        string_ref::StrRef,
        utils::{MaybeInvalid, Reference},
    },
};

mod guard {
    use std::ops::Deref;

    use crate::{
        formula::function::Function,
        problem::{cell::MemoryCell, step::Step},
    };

    #[derive(Hash, Clone, Copy, PartialEq, Eq, Debug)]
    pub struct Guard<T>(T);

    impl<T> Deref for Guard<T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<T> From<T> for Guard<T> {
        fn from(value: T) -> Self {
            Guard(value)
        }
    }

    pub type GuardedFunction<'bump> = Guard<Function<'bump>>;
    pub type GuardedStep<'bump> = Guard<Step<'bump>>;
    pub type GuardedMemoryCell<'bump> = Guard<MemoryCell<'bump>>;
}

#[derive(Debug)]
pub struct Environement<'bump> {
    /// the main memory
    container: &'bump Container<'bump>,

    /// some hash map to quickly turn [String] likes into [Sort] or [Function] during parsing.
    ///
    /// This is basically the non-variable bounded names
    ///
    /// This one is for [Sort]
    sort_hash: HashMap<&'bump str, Sort<'bump>>,
    /// That one for [Function]s
    function_hash: HashMap<String, Function<'bump>>,

    /// List of things to initialize
    /// 
    /// Those are recurive structure or immutable structure which cannot be built at once.
    /// Instead we define them incrementally and once the parsing is done, we call [Self::finalize()]
    /// 
    /// We use [Guard<T>] to ensure only the trait we know won't call the underlying `T` in
    /// that are not initialized yet.
    /// 
    /// This one is for [Function]
    functions_initialize: HashMap<GuardedFunction<'bump>, Option<InnerFunction<'bump>>>,
    /// For [Step][crate::problem::step::Step]
    steps_initialize: HashMap<GuardedStep<'bump>, Option<InnerStep<'bump>>>,
    /// For [MemoryCell][crate::problem::cell::MemoryCell]
    cells_initialize: HashMap<GuardedMemoryCell<'bump>, Option<InnerMemoryCell<'bump>>>,
}

/// Declare the sort
pub fn declare_sorts<'a, 'bump>(env: &mut Environement<'bump>, ast: &ASTList<'a>) -> Result<(), E> {
    ast.into_iter()
        .filter_map(|ast| match ast {
            AST::Declaration(d) => match d.as_ref() {
                Declaration::Type(dt) => Some(dt),
                _ => None,
            },
            _ => None,
        })
        .try_for_each(|s| {
            let name = s.name();
            if env.sort_hash.contains_key(name) {
                err(merr!(*s.get_name_span(); "the sort name {} is already in use", name))
            } else {
                let sort = Sort::new_regular(env.container, name.to_owned());
                env.sort_hash
                    .insert(sort.name(), sort)
                    .ok_or_else(|| {
                        merr!(*s.get_name_span();
                        "!UNREACHABLE!(line {} in {}) \
The sort name {} somehow reintroduced itself in the hash",
                        line!(), file!(), name)
                    })
                    .map(|_| ())
            }
        })
}

/// declare the user function (e.g., tuple & co)
pub fn declare_functions<'a, 'bump>(
    env: &mut Environement<'bump>,
    ast: &ASTList<'a>,
) -> Result<(), E> {
    ast.into_iter()
        .filter_map(|ast| match ast {
            AST::Declaration(b) => match b.as_ref() {
                Declaration::Function(f) => Some(f),
                _ => None,
            },
            _ => None,
        })
        .try_for_each(|fun| {
            let Ident {
                span,
                content: name,
            } = fun.name();
            if env.function_hash.contains_key(name) {
                err(merr!(span; "the function name {} is already in use", name))
            } else {
                let input_sorts: Result<Vec<_>, _> = fun
                    .args()
                    .map(|idn| get_sort(env, idn.span, idn.content))
                    .collect();
                let output_sort = {
                    let idn = fun.out();
                    get_sort(env, idn.span, idn.content)
                }?;
                let fun =
                    Function::new_user_term_algebra(env.container, name, input_sorts?, output_sort)
                        .main;
                env.function_hash
                    .insert(fun.name().to_string(), fun)
                    .ok_or_else(|| {
                        merr!(span;
                        "!UNREACHABLE!(line {} in {}) \
The function name {} somehow reintroduced itself in the hash",
                        line!(), file!(), name)
                    })
                    .map(|_| ())
            }
        })
}

/// Declare memory cells and steps.
///
/// The functions are also added to the list of things to initialize as the
/// they are kept empty. For instance a step might depend on itself.
pub fn declare_steps_and_cells<'a, 'bump>(
    env: &mut Environement<'bump>,
    ast: &ASTList<'a>,
) -> Result<(), E> {
    ast.into_iter()
        .filter_map(|ast| match ast {
            AST::Declaration(b) => match Box::as_ref(b) {
                Declaration::Cell(f) => Some(extra::MAsFunction::Cell(f)),
                _ => None,
            },
            AST::Step(b) => Some(extra::MAsFunction::Step(Box::as_ref(b))),
            _ => None,
        })
        // extract only the terms that matter
        // that is the declarations of cells and steps
        // and turn them into a MAsFunction to generically take care of them
        .try_for_each(|fun| {
            let SnN { span, name } = fun.name();
            if env.function_hash.contains_key(name) {
                err(merr!(*span; "the step/cell/function name {} is already in use", name))
            } else {
                // the input sorts (will gracefully error out later if a sort is undefined)
                let input_sorts: Result<Vec<_>, _> = fun
                    .args()
                    .into_iter()
                    .map(|idn| get_sort(env, *idn.span, idn.name))
                    .collect();
                // the output sort
                let output_sort = {
                    let idn = fun.out();
                    get_sort(env, *idn.span, idn.name)
                }?;
                // built an uninitialized function
                let fun = Function::new_uninit(
                    env.container,
                    Some(name),
                    Some(input_sorts?),
                    Some(output_sort),
                );

                // add the function to the list of things to initialize
                let not_already_in = env.functions_initialize.insert(fun.into(), None).is_none();
                assert!(not_already_in);

                // add the function the map of function for faster parsing
                env.function_hash
                    .insert(fun.name().to_string(), fun)
                    .ok_or_else(|| {
                        merr!(*span;
                        "!UNREACHABLE!(line {} in {}) \
The step/cell/function name {} somehow reintroduced itself in the hash",
                        line!(), file!(), name)
                    })
                    .map(|_| ())
            }
        })
}

/// Find the [Sort] in already declared in [Environement::sort_hash]
fn get_sort<'a, 'bump>(
    env: &Environement<'bump>,
    span: Span<'a>,
    str: implderef!(str),
) -> Result<Sort<'bump>, E> {
    env.sort_hash
        .get(Deref::deref(&str))
        .ok_or_else(|| merr!(span; "undefined sort {}", Deref::deref(&str)))
        .map(|s| *s)
}

/// Find the [Function] in already declared in [Environement::sort_function]
fn get_function<'a, 'bump>(
    env: &Environement<'bump>,
    span: Span<'a>,
    str: implderef!(str),
) -> Result<Function<'bump>, E> {
    env.function_hash
        .get(Deref::deref(&str))
        .ok_or_else(|| merr!(span; "undefined function {}", Deref::deref(&str)))
        .map(|s| *s)
}

impl<'bump> MaybeInvalid for Environement<'bump> {
    fn valid(&self) -> bool {
        todo!()
    }
}

impl<'bump> Environement<'bump> {
    pub fn finalize(&mut self) {
        assert!(self.valid());

        fn finalize_hash_map<T>(h: &mut HashMap<Guard<T>, Option<T::Inner>>)
        where
            T: Reference,
        {
            for (g, fun) in std::mem::take(h) {
                if let Some(fun) = fun {
                    unsafe { g.overwrite(fun) }
                } else {
                    unreachable!()
                }
            }
        }

        finalize_hash_map(&mut self.functions_initialize);
        finalize_hash_map(&mut self.steps_initialize);
        finalize_hash_map(&mut self.cells_initialize);
    }
}
