use std::{collections::HashMap, ops::Deref};

use pest::Span;

use self::{
    guard::{GuardedFunction, GuardedMemoryCell, GuardedStep},
    parsable_trait::VarProxy,
};

use super::{
    ast::{
        extra::{self, AsFunction, SnN},
        ASTList, Declaration, DeclareType, Ident, Term, AST,
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
struct Macro<'bump, 'a> {
    // name: &'a str,
    args: Vec<(&'a str, Variable<'bump>)>,
    content: ast::Term<'a>,
}

#[derive(Debug)]
pub struct Environement<'bump, 'str> {
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
    macro_hash: HashMap<&'str str, Macro<'bump, 'str>>,

    /// # Macro look up table
    step_lut_to_parse: HashMap<&'str str, ast::Step<'str>>,

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
pub fn declare_sorts<'a, 'bump>(
    env: &mut Environement<'bump, 'a>,
    ast: &ASTList<'a>,
) -> Result<(), E> {
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
                err(merr(
                    *s.get_name_span(),
                    f!("the sort name {} is already in use", name),
                ))
            } else {
                let sort = Sort::new_regular(env.container, name.to_owned());
                env.sort_hash
                    .insert(sort.name(), sort)
                    .ok_or_else(|| {
                        merr(
                            *s.get_name_span(),
                            f!(
                                "!UNREACHABLE!(line {} in {}) \
The sort name {} somehow reintroduced itself in the hash",
                                line!(),
                                file!(),
                                name
                            ),
                        )
                    })
                    .map(|_| ())
            }
        })
}

/// declare the user function (e.g., tuple & co)
pub fn declare_functions<'a, 'bump>(
    env: &mut Environement<'bump, 'a>,
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
                err(merr(
                    span,
                    f!("the function name {} is already in use", name),
                ))
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
                        merr(
                            span,
                            f!(
                                "!UNREACHABLE!(line {} in {}) \
The function name {} somehow reintroduced itself in the hash",
                                line!(),
                                file!(),
                                name
                            ),
                        )
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
    env: &mut Environement<'bump, 'a>,
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
                err(merr(
                    *span,
                    f!("the step/cell/function name {} is already in use", name),
                ))
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
                    err(merr(
                        *span,
                        f!("already in the list of things to initialize"),
                    ))?;
                }

                // add the function the map of function for faster parsing
                env.function_hash
                    .insert(fun.name().to_string(), fun)
                    .ok_or_else(|| {
                        merr(
                            *span,
                            f!("!UNREACHABLE!(line {} in {}; {})", line!(), file!(), name),
                        )
                    })
                    .map(|_| ())
            }
        })
}

fn declare_let<'bump, 'a>(env: &mut Environement<'bump, 'a>, ast: &ASTList<'a>) -> Result<(), E> {
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
                err(merr(*span, f!("the macro {}! is already in use", name)))
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
fn get_function<'a, 'bump>(
    env: &Environement<'bump, 'a>,
    span: Span<'a>,
    str: implderef!(str),
) -> Result<Function<'bump>, E> {
    env.function_hash
        .get(Deref::deref(&str))
        .ok_or_else(|| merr(span, f!("undefined function {}", Deref::deref(&str))))
        .map(|s| *s)
}

impl<'bump, 'a> MaybeInvalid for Environement<'bump, 'a> {
    fn valid(&self) -> bool {
        todo!()
    }
}

impl<'bump, 'a> Environement<'bump, 'a> {
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
            step_lut_to_parse: Default::default(),
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

    use if_chain::if_chain;
    use itertools::Itertools;
    use pest::Span;

    use crate::{
        f,
        formula::{
            self,
            formula::RichFormula,
            function::{
                self,
                builtin::{IF_THEN_ELSE, IF_THEN_ELSE_TA, INPUT},
                signature::{CheckError, Signature},
                Function, InnerFunction, term_algebra::TermAlgebra, traits::MaybeEvaluatable,
            },
            sort::{
                builtins::{BOOL, CONDITION, MESSAGE, STEP},
                sort_proxy::SortProxy,
                Sort,
            },
            variable::Variable,
        },
        match_as_trait,
        parser::{
            ast::{self, extra::SnN, Macro, VariableBinding},
            err, merr,
            parser::{get_function, get_sort},
            IntoRuleResult, E,
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
            env: &Environement<'bump, 'str>,
            bvars: &mut Vec<(&'str str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E>;
    }

    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::LetIn<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump, 'a>,
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
            Ok(t2.apply_substitution([vn], [&t1]))
        }
    }
    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::IfThenElse<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump, 'a>,
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
                SortProxy::expects(&eb, e).into_rr(self.span)?
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
            env: &Environement<'bump, 'a>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            expected_sort
                .into_iter()
                .try_for_each(|s| s.expects(MESSAGE.as_sort()).into_rr(self.span))?;

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

                    // ensures the name is free
                    if env.function_hash.contains_key(variable.name()) {
                        return err(merr(
                            variable.0.span,
                            f!("the name {} is already taken", variable.name()),
                        ));
                    }

                    let SnN { span, name } = type_name.into();

                    let var = Variable {
                        id,
                        sort: get_sort(env, *span, name)?,
                    };

                    // sneakly expand `bvars`
                    // we need this here to keep the name
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
                Function::new_find_such_that(env.container, vars, condition, left, right);

            Ok(match state {
                State::Low => f.f(fvars.into_iter().map(RichFormula::from)),
                _ => todo!(),
            })
        }
    }
    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Quantifier<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump, 'a>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            let ast::Quantifier {
                kind,
                span,
                vars,
                content,
                ..
            } = self;

            let es = match state {
                State::Convert | State::High => BOOL.as_sort().into(),
                State::Low => CONDITION.as_sort().into(),
            };
            expected_sort
                .into_iter()
                .try_for_each(|s| s.expects(es).into_rr(*span))?;

            let bn = bvars.len();

            bvars.reserve(vars.into_iter().len());
            let vars: Result<Vec<_>, _> = vars
                .into_iter()
                .enumerate()
                .map(|(i, v)| {
                    let id = i + bn;
                    let VariableBinding {
                        variable,
                        type_name,
                        ..
                    } = v;

                    let vname = variable.name();
                    // ensures the name is free
                    if env.function_hash.contains_key(vname) {
                        return err(merr(
                            variable.0.span,
                            f!("the name {} is already taken", vname),
                        ));
                    }

                    let SnN { span, name } = type_name.into();

                    let var = Variable {
                        id,
                        sort: get_sort(env, *span, name)?,
                    };

                    // sneakly expand `bvars`
                    // we need this here to keep the name
                    let content = (variable.name(), var.into());
                    bvars.push(content);

                    Ok(var)
                })
                .collect();
            let vars = vars?;

            // parse body
            let content = content.parse(env, bvars, state, Some(es.into()))?;

            // remove bounded variables from pile
            bvars.truncate(bn);

            let q = {
                let status = match state {
                    State::Convert | State::High => formula::quantifier::Status::Bool,
                    State::Low => formula::quantifier::Status::Condition,
                };
                match kind {
                    ast::QuantifierKind::Forall => formula::quantifier::Quantifier::Forall {
                        variables: vars,
                        status,
                    },
                    ast::QuantifierKind::Exists => formula::quantifier::Quantifier::Exists {
                        variables: vars,
                        status,
                    },
                }
            };

            Ok(match state {
                State::Convert | State::High => RichFormula::Quantifier(q, Box::new(content)),
                State::Low => {
                    let fq = Function::new_quantifier_from_quantifier(
                        env.container,
                        q,
                        Box::new(content),
                    );

                    let args = match fq.as_ref() {
                        function::InnerFunction::TermAlgebra(TermAlgebra::Quantifier(q)) => {
                            q.free_variables.iter()
                        }
                        _ => unreachable!(),
                    }
                    .map(RichFormula::from);

                    fq.f(args)
                }
            })
        }
    }
    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Application<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump, 'a>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            match self {
                ast::Application::ConstVar { span, content } => {
                    // check if it is a variable
                    bvars.iter().find(|(s, _)| s == content).map(|(_, v)| {
                        let VarProxy { id, sort } = v;
                        let sort = expected_sort.clone()
                            .map(|es| sort.unify(&es).into_rr(*span))
                            .unwrap_or_else(|| {
                                Into::<Option<Sort>>::into(sort)
                                    .ok_or_else(|| merr(*span, f!("can't infer sort")))
                            })?;

                        Ok(Variable { id: *id, sort }.into())
                    })
                    // otherwise look for a function
                    .unwrap_or_else(|| get_function(env, *span, *content).and_then(|f| {

                        // TODO: check arity

                        // get the evaluated version if needed
                        let f_eval = match state {
                            State::Convert | State::High => f.as_term_algebra().maybe_get_evaluated().unwrap_or(f),
                            State::Low => f
                        };

                        match expected_sort.map(|s| (s.clone(), s.into())) {
                            None => Ok(f_eval.f([])),
                            Some((s, None)) => {
                                if let Some(s2) = f.fast_outsort() {
                                    s.set(s2)
                                }
                                Ok(f_eval.f([]))
                            },
                            Some((_, Some(s))) => if_chain!{
                                if let Some(s2) = f.fast_outsort();
                                if s2 != s;
                                then {
                                    err(merr(*span, f!("wrong sort: got {}, expected {}", s2.name(), s.name())))
                                } else {
                                    Ok(f_eval.f([]))
                                }
                            }
                        }
                    }))
                }
                ast::Application::Application {
                    span,
                    function,
                    args,
                } => {
                    get_function(env, *span, function.0.content.content).and_then(|f| {
                        // TODO: arity
                        let signature = f.signature();

                        // get the evaluated version if needed
                        let f_eval = match state {
                            State::Convert | State::High => {
                                f.as_term_algebra().maybe_get_evaluated().unwrap_or(f)
                            }
                            State::Low => f,
                        };

                        // parse further
                        let n_args: Result<Vec<_>, _> = signature
                            .args()
                            .into_iter()
                            .zip(args.iter())
                            .map(|(es, t)| t.parse(env, bvars, state, Some(es)))
                            .collect();
                        let n_args = n_args?;
                        // check arity & co
                        let _ = match signature.check_rich_formulas(&n_args) {
                            Ok(_) => Ok(()),
                            Err(CheckError::SortError { position, error }) => match position {
                                Some(i) => err(merr(args[i].span, f!("{}", error))),
                                None => err(merr(*span, f!("{}", error))),
                            },
                            Err(e) => err(merr(*span, f!("{}", e))),
                        }?;

                        // check output sort
                        let _ = expected_sort
                            .map(|es| es.unify(&signature.out()))
                            .transpose()
                            .into_rr(*span)?;

                        Ok(f_eval.f(n_args))
                    })
                }
            }
        }
    }
    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::AppMacro<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump, 'a>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            let Self {
                span: main_span,
                inner,
            } = self;

            match inner {
                ast::InnerAppMacro::Msg(app) | ast::InnerAppMacro::Cond(app) => {
                    let step_as_term = app.parse(env, bvars, state, Some(STEP.as_sort().into()))?;

                    let args = if let RichFormula::Fun(_, args) = &step_as_term {
                        Ok(args)
                    } else {
                        err(
                            merr(app.span(), f!("this can only be a plain reference to a step (not just a term of sort {}))", STEP.name()))
                        )
                    }?;

                    let step = env.step_lut_to_parse.get(app.name()).ok_or_else(|| {
                        merr(
                            app.name_span(),
                            f!("{} is not a known step name", app.name()),
                        )
                    })?;

                    let nbvars: Result<Vec<_>, _> = step
                        .args
                        .into_iter()
                        .enumerate()
                        .map(|(i, v)| {
                            let name = v.variable.name();
                            let sort = env.sort_hash.get(v.type_name.name()).ok_or_else(|| {
                                merr(
                                    v.type_name.name_span(),
                                    f!("{} is not a known type", v.type_name.name()),
                                )
                            })?;
                            Ok((
                                name,
                                VarProxy {
                                    id: i + 1,
                                    sort: sort.into(),
                                },
                            ))
                        })
                        .chain([Ok((
                            "in",
                            VarProxy {
                                id: 0,
                                sort: MESSAGE.as_sort().into(),
                            },
                        ))])
                        .collect();
                    let mut nbvars = nbvars?;
                    let n = bvars.len();

                    let (to_parse, n_es) = match inner {
                        ast::InnerAppMacro::Msg(_) => (&step.message, MESSAGE.as_sort()),
                        ast::InnerAppMacro::Cond(_) => (&step.condition, CONDITION.as_sort()),
                        _ => unreachable!(),
                    };
                    if let Some(es) = expected_sort {
                        let n_es_2 = SortProxy::from(n_es).unify(&es).into_rr(*main_span)?;
                        assert_eq!(n_es, n_es_2);
                    };

                    let term = to_parse.parse(env, &mut nbvars, state, Some(n_es.into()))?;

                    let input = INPUT.f([step_as_term.clone()]);
                    Ok(term.apply_substitution(0..=n, [&input].into_iter().chain(args)))
                }
                ast::InnerAppMacro::Other { name, args } => {
                    let mmacro = env.macro_hash.get(name.name()).ok_or_else(|| {
                        merr(name.span(), f!("{} is not a known macro", name.name()))
                    })?;

                    let args: Vec<_> = if mmacro.args.len() == args.len() {
                        mmacro
                            .args
                            .iter()
                            .zip(args)
                            .map(|((_, v), arg)| {
                                arg.parse(env, bvars, state, Some(v.sort().into()))
                            })
                            .collect()
                    } else {
                        err(merr(
                            *main_span,
                            f!(
                                "not enough arguments: expected {}, got {}",
                                mmacro.args.len(),
                                args.len()
                            ),
                        ))
                    }?;

                    let term = {
                        let mut bvars = mmacro
                            .args
                            .iter()
                            .map(|(s, v)| (*s, (*v).into()))
                            .collect_vec();
                        mmacro.content.parse(env, &mut bvars, state, expected_sort)
                    }?;

                    Ok(term.apply_substitution(mmacro.args.iter().map(|(_, v)| v.id), &args))
                }
            }
        }
    }
    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Infix<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump, 'a>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            // let n_es = match state {
            //     State::Convert | State::High => BOOL.as_sort().into(),
            //     State::Low => todo!(),
            // };

            todo!()
        }
    }
    impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Term<'a> {
        type R = RichFormula<'bump>;

        fn parse(
            &self,
            env: &Environement<'bump, 'a>,
            bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
            state: State,
            expected_sort: Option<SortProxy<'bump>>,
        ) -> Result<Self::R, E> {
            match_as_trait!(ast::InnerTerm, |x| in &self.inner => LetIn | If | Fndst | Quant | Application | Infix | Macro
                    {x.parse(env, bvars, state, expected_sort)})
        }
    }
}
