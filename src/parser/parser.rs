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
        formula::RichFormula,
        function::{self, Function, InnerFunction},
        sort::{InnerSort, Sort},
        variable::Variable,
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

#[derive(Hash, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
struct Macro<'bump> {
    name: String,
    args: Vec<Variable<'bump>>,
    content: RichFormula<'bump>,
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
    /// For [Macro]s
    macro_hash: HashMap<String, Macro<'bump>>,

    /// List of things to initialize
    ///
    /// Those are recurive structure or immutable structure which cannot be built at once.
    /// Instead we define them incrementally and once the parsing is done, we call [Self::finalize()]
    ///
    /// We use [`Guard<T>`] to ensure only the trait we know won't call the underlying `T` in
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
                let err_check = env.functions_initialize.insert(fun.into(), None);
                // errors out if it is already in the list
                // NB: no UB because "uninitialized" is another state.
                // (might "gracefully" crash later though)
                if let Some(_) = err_check {
                    err(merr!(*span; "already in the list of things to initialize"))?;
                }

                // add the function the map of function for faster parsing
                env.function_hash
                    .insert(fun.name().to_string(), fun)
                    .ok_or_else(|| {
                        merr!(*span;
                        "!UNREACHABLE!(line {} in {}; {})",
                        line!(), file!(), name)
                    })
                    .map(|_| ())
            }
        })
}

fn declare_let<'bump, 'a>(env: &mut Environement<'bump>, ast: &ASTList<'a>) -> Result<(), E> {
    ast.into_iter()
        .filter_map(|ast| match ast {
            AST::Let(b) => Some(b.as_ref()),
            _ => None,
        })
        .try_for_each(|mlet| {
            let super::ast::Macro { name, term, .. } = mlet;
            let SnN { span, name } = name.into();
            // TODO: no hard-coded values
            if env.macro_hash.contains_key(name) || ["msg", "cond"].contains(&name) {
                err(merr!(*span; "the macro {}! is already in use", name))
            } else {
                // the input sorts (will gracefully error out later if a sort is undefined)
                let input_sorts: Result<Vec<_>, _> = mlet
                    .args()
                    .into_iter()
                    .map(|idn| get_sort(env, *idn.span, idn.name))
                    .collect();

                todo!()
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
    pub fn new(
        container: &'bump Container<'bump>,
        sort_hash: implvec!(Sort<'bump>),
        function_hash: implvec!(function::Function<'bump>),
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
            macro_hash: Default::default(),
            functions_initialize: Default::default(),
            steps_initialize: Default::default(),
            cells_initialize: Default::default(),
        }
    }

    pub fn finalize(&mut self) {
        fn finalize_hash_map<T>(h: &mut HashMap<Guard<T>, Option<T::Inner>>)
        where
            T: Reference,
        {
            std::mem::take(h)
                .into_iter()
                // This returns shortcuts to `None` if `fun` is `None`
                .try_for_each(|(g, fun)| fun.map(|fun| unsafe { g.overwrite(fun) }))
                .expect("unreachable") // should never crash
        }

        let Environement {
            functions_initialize,
            steps_initialize,
            cells_initialize,
            ..
        } = self;

        finalize_hash_map(functions_initialize);
        finalize_hash_map(steps_initialize);
        finalize_hash_map(cells_initialize);

        assert!(self.valid(), "something went wrong while initializing");
    }
}

mod parsable_trait {
    use std::{borrow::BorrowMut, cell::RefCell, collections::HashSet, rc::Rc};

    use itertools::Itertools;
    use pest::Span;

    use crate::{
        formula::{
            formula::RichFormula,
            function::{
                builtin::{IF_THEN_ELSE, IF_THEN_ELSE_TA},
                Function,
            },
            sort::{
                builtins::{BOOL, CONDITION, MESSAGE},
                Sort,
            },
            variable::Variable,
        },
        parser::{
            ast::{self, extra::SnN},
            err, merr,
            parser::get_sort,
            E,
        },
    };

    use super::Environement;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
    pub enum State {
        High,
        Low,
        Convert,
    }

    impl Default for State {
        fn default() -> Self {
            Self::High
        }
    }

    /// A way to emulate sort variables for type inference
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Default)]
    pub struct SortProxy<'bump>(Rc<RefCell<Option<Sort<'bump>>>>);

    impl<'bump> SortProxy<'bump> {
        fn match_sort<'a>(&self, s: Sort<'bump>, span: Span<'a>) -> Result<(), E> {
            match self.0.borrow().clone() {
                Some(s2) if s2 == s => Ok(()),
                None => {
                    // if not defined yet, assign a sort
                    *RefCell::borrow_mut(&self.0.as_ref()) = Some(s);
                    Ok(())
                }
                Some(s2) => err(merr!(span; "wrong sort: {} instead of {}", s2.name(), s.name())),
            }
        }
    }

    impl<'bump> From<Sort<'bump>> for SortProxy<'bump> {
        fn from(value: Sort<'bump>) -> Self {
            Self(Rc::new(RefCell::new(Some(value))))
        }
    }

    impl<'bump> Into<Option<Sort<'bump>>> for SortProxy<'bump> {
        fn into(self) -> Option<Sort<'bump>> {
            self.0.borrow().clone()
        }
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
    pub struct VarProxy<'bump> {
        id: usize,
        sort: SortProxy<'bump>,
    }

    impl<'bump> From<Variable<'bump>> for VarProxy<'bump> {
        fn from(value: Variable<'bump>) -> Self {
            Self {
                id: value.id,
                sort: value.sort.into(),
            }
        }
    }

    pub trait Parsable<'bump, 'str>
    where
        'bump: 'str,
    {
        type R;
        fn parse(
            &self,
            env: &Environement<'bump>,
            bvars: &mut Vec<(&'str str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E>;
    }

    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::LetIn<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            // current length of the pile of variable
            // to be reused for variable indexing, and troncating the pile
            let vn = bvars.len();

            // retrieve data
            let ast::LetIn { var, t1, t2, .. } = self;

            // defined a new variable of unknown type
            let v = VarProxy {
                id: vn,
                sort: Default::default(),
            };

            // parse t1 expecting the unknown sort
            let t1 = t1.parse(env, bvars, state, Some(v.sort.clone()))?;

            // parse t2
            let t2 = {
                bvars.push((var.name(), v.clone())); // add var to the pile
                let t2 = t2.parse(env, bvars, state, expected_sort.clone())?;
                bvars.truncate(vn); // remove it from the pile
                t2
            };

            // replace `v` by its content: `t1`
            Ok(t2.apply_substitution(&[vn], &[t1]))
        }
    }
    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::IfThenElse<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            // generate the expected sorts
            let (ec, eb) = match state {
                State::High | State::Convert => (BOOL.as_sort().into(), Default::default()),
                State::Low => (CONDITION.as_sort().into(), MESSAGE.as_sort().into()),
            };

            let expected_sort = if let State::Low = state {
                Some(MESSAGE.as_sort().into())
            } else {
                expected_sort
            };

            // check sort
            if let Some(e) = expected_sort.and_then(|s| s.into()) {
                SortProxy::match_sort(&eb, e, self.span)?
            }

            let ast::IfThenElse {
                condition,
                left,
                right,
                ..
            } = self;

            let condition = condition.parse(env, bvars, state, Some(ec))?;
            let left = left.parse(env, bvars, state, Some(eb.clone()))?;
            let right = right.parse(env, bvars, state, Some(eb))?;

            Ok(match state {
                State::High | State::Convert => IF_THEN_ELSE.clone(),
                State::Low => IF_THEN_ELSE_TA.clone(),
            }
            .f([condition, left, right]))
        }
    }

    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::FindSuchThat<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            expected_sort
                .into_iter()
                .try_for_each(|s| s.match_sort(MESSAGE.as_sort(), self.span))?;

            let ast::FindSuchThat {
                vars,
                condition,
                left,
                right,
                ..
            } = self;

            // parse the default case without the extra variables
            let right = right.parse(env, bvars, State::Low, Some(MESSAGE.as_sort().into()))?;

            // for unique ids and truncate
            let bn = bvars.len();

            // build the bound variables
            bvars.reserve(vars.into_iter().len());
            let vars: Result<Vec<_>, _> = vars
                .into_iter()
                .enumerate()
                .map(|(i, v)| {
                    let id = i + bn;
                    let ast::VariableBinding {
                        variable,
                        type_name,
                        ..
                    } = v;
                    let SnN { span, name } = type_name.into();

                    let var = Variable {
                        id,
                        sort: get_sort(env, *span, name)?,
                    };

                    // sneakly expand `bvars`
                    let content = (variable.name(), var.into());
                    bvars.push(content);

                    Ok(var)
                })
                .collect();
            let vars = vars?;

            // parse the rest
            let condition =
                condition.parse(env, bvars, State::Low, Some(CONDITION.as_sort().into()))?;
            let left = left.parse(env, bvars, State::Low, Some(MESSAGE.as_sort().into()))?;

            // remove variables
            bvars.truncate(bn);

            let (f /* the function */, fvars /* the free vars */) =
                Function::new_find_such_that(env.container, vars.clone(), condition, left, right);

            Ok(match state {
                State::Low => f.f(fvars.into_iter().map(RichFormula::from)),
                _ => todo!(),
            })
        }
    }
    // impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Quantifier<'a> {}
    // impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Application<'a> {}
    // impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::AppMacro<'a> {}
    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Term<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            todo!()
        }
    }
}
