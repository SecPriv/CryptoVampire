use std::fmt::{self};

use cryptovampire_smt::{SortedVar, VarInner};
use if_chain::if_chain;

use self::display::{SmtDisplayer, SmtEnv};
use crate::environement::environement::Environement;
use crate::environement::traits::{KnowsRealm, Realm};
use crate::formula::file_descriptior::GeneralFile;
use crate::formula::file_descriptior::axioms::{Axiom, Rewrite, RewriteKind};
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::RichFormula;
use crate::formula::function::inner::booleans::{Booleans, Connective};
use crate::formula::function::signature::Signature;
use crate::formula::function::{Function, InnerFunction};
use crate::formula::quantifier::Quantifier;
use crate::formula::sort::Sort;
use crate::formula::variable::Variable;
use crate::{FromEnv, SubtermKind};

pub type SmtFile<'bump> = cryptovampire_smt::SmtFile<Sort<'bump>, Function<'bump>>;
pub type Smt<'bump> = cryptovampire_smt::Smt<Sort<'bump>, Function<'bump>>;
pub type SmtFormula<'bump> = cryptovampire_smt::SmtFormula<Sort<'bump>, Function<'bump>>;
pub type SmtCons<'bump> = cryptovampire_smt::SmtCons<Sort<'bump>, Function<'bump>>;

mod display;

fn fun_list_fmt<I: Iterator<Item = impl fmt::Display>>(
    f: &mut fmt::Formatter<'_>,
    str: &str,
    iter: I,
) -> fmt::Result {
    write!(f, "({} ", str)?;
    for e in iter {
        write!(f, "{} ", e)?;
    }
    write!(f, ")")
}

macro_rules! unpack_args {
    ([$($arg:ident),*] = $args:expr; $do:block) => {{
        let mut iter = $args.into_iter();
        $(
            let $arg = if let Some(tmp) = iter.next() {
                tmp
            } else {
                panic!("not enough arguments")
            };
        )*
        assert!(iter.next().is_none(), "too many arguments");
        $do
    }};
}

fn vars_to_sorted_vars<'bump>(vars: &[Variable<'bump>]) -> Vec<SortedVar<Sort<'bump>>> {
    vars.iter()
        .map(|v| SortedVar {
            var: VarInner::Int(v.get_unique_id()),
            sort: v.sort,
        })
        .collect()
}

impl<'a, 'bump> From<&'a RichFormula<'bump>> for SmtFormula<'bump> {
    fn from(formula: &'a RichFormula<'bump>) -> Self {
        match formula {
            RichFormula::Var(v) => SmtFormula::Var(VarInner::Int(v.get_unique_id())),
            RichFormula::Quantifier(q, arg) => match q {
                Quantifier::Exists { variables } => SmtFormula::Exists(
                    vars_to_sorted_vars(variables),
                    Box::new(arg.as_ref().into()),
                ),
                Quantifier::Forall { variables } => SmtFormula::Forall(
                    vars_to_sorted_vars(variables),
                    Box::new(arg.as_ref().into()),
                ),
            },
            RichFormula::Fun(f, args) => {
                let mut args = args.iter().map(|f| f.as_ref().into()).collect();

                match f.as_inner() {
                    InnerFunction::TermAlgebra(_)
                    // | InnerFunction::Nonce(_)
                    | InnerFunction::Step(_)
                    | InnerFunction::Predicate(_)
                    | InnerFunction::Tmp(_)
                    | InnerFunction::Skolem(_)
                    | InnerFunction::Name(_)
                    | InnerFunction::EvaluatedFun(_)
                    | InnerFunction::Evaluate(_) => SmtFormula::Fun(*f, args),
                    InnerFunction::Subterm(subterm) => {
                        let kind = subterm.kind();

                        match kind {
                            SubtermKind::Regular(_) => SmtFormula::Fun(*f, args),
                            SubtermKind::Vampire(_) => {
                                unpack_args!([a, b] =  args; {
                                    SmtFormula::Subterm(*f, Box::new(a), Box::new(b))
                                })
                            }
                        }
                    }
                    InnerFunction::IfThenElse(_) => {
                        unpack_args!([c, l, r] = args; {
                            SmtFormula::Ite(Box::new(c), Box::new(l), Box::new(r))
                        })
                    }
                    InnerFunction::Bool(c) => match c {
                        Booleans::Equality(_) => SmtFormula::Eq(args),
                        Booleans::Connective(c) => match c {
                            Connective::True => SmtFormula::True,
                            Connective::False => SmtFormula::False,
                            Connective::And => SmtFormula::And(args),
                            Connective::Or => SmtFormula::Or(args),
                            Connective::Not => SmtFormula::Not(Box::new(args.pop().unwrap())),
                            Connective::Implies => {
                                unpack_args!([a, b] = args; {
                                    SmtFormula::Implies(Box::new(a), Box::new(b))
                                })
                            }
                            // Connective::Iff => SmtFormula::Eq(args),
                        },
                    },
                    // InnerFunction::Invalid(_) => unreachable!("the function is invalid")
                }
            }
        }
    }
}

pub(crate) trait SmtDisplay<'bump>: Sized {
    // fn as_display(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_;

    fn into_display(self, env: &impl KnowsRealm) -> impl fmt::Display + 'bump;

    fn as_display(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_;

    fn prop<D, T>(&self, disp: SmtDisplayer<D, T>) -> SmtDisplayer<D, &Self> {
        disp.propagate(self)
    }

    fn default_display(&self) -> impl fmt::Display + '_ {
        self.as_display(&Realm::Symbolic)
    }
}

impl<'bump> SmtDisplay<'bump> for SmtFormula<'bump> {
    fn into_display(self, env: &impl KnowsRealm) -> impl fmt::Display + 'bump {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }

    fn as_display(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }
}

// impl<'bump> SmtFormula<'bump> {
//     pub fn default_display(&self) -> impl fmt::Display + '_ {
//         SmtDisplayer {
//             env: SmtEnv {
//                 realm: Realm::Symbolic,
//             },
//             content: self,
//         }
//     }

//     pub fn as_display(self, env: &impl KnowsRealm) -> impl fmt::Display + 'bump {
//         SmtDisplayer {
//             env: SmtEnv {
//                 realm: env.get_realm(),
//             },
//             content: self,
//         }
//     }

//     pub fn as_display_ref(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
//         SmtDisplayer {
//             env: SmtEnv {
//                 realm: env.get_realm(),
//             },
//             content: self,
//         }
//     }

//     fn prop<D, T>(&self, disp: SmtDisplayer<D, T>) -> SmtDisplayer<D, &Self> {
//         disp.propagate(self)
//     }
// }

impl<'bump> FromEnv<'bump, Axiom<'bump>> for Smt<'bump> {
    fn with_env(env: &Environement<'bump>, ax: Axiom<'bump>) -> Self {
        match ax {
            Axiom::Comment(str) => Smt::Comment(str.into()),
            Axiom::Base { formula } => Smt::Assert(formula.as_ref().into()),
            Axiom::Theory { formula } => {
                let f = formula.as_ref().into();
                if env.use_assert_theory() {
                    Smt::AssertTh(f)
                } else {
                    Smt::Assert(f)
                }
            }
            Axiom::Query { formula } => {
                let f = formula.as_ref().into();
                if env.use_assert_not() {
                    Smt::AssertNot(f)
                } else {
                    Smt::Assert(SmtFormula::Not(Box::new(f)))
                }
            }
            Axiom::Rewrite { rewrite } => {
                let Rewrite {
                    kind,
                    vars,
                    pre,
                    post,
                } = *rewrite;
                let pre = pre.as_ref().into();
                let post = post.as_ref().into();
                if env.no_rewrite() {
                    Smt::Assert(SmtFormula::Forall(
                        vars_to_sorted_vars(&vars),
                        Box::new(if kind == RewriteKind::Bool {
                            // SmtFormula::Implies(Box::new(pre), Box::new(post))
                            SmtFormula::Eq(vec![pre, post])
                        } else {
                            SmtFormula::Eq(vec![pre, post])
                        }),
                    ))
                } else {
                    Smt::DeclareRewrite {
                        rewrite_fun: kind,
                        vars: vars_to_sorted_vars(&vars),
                        lhs: Box::new(pre),
                        rhs: Box::new(post),
                    }
                }
            }
            Axiom::Ground { sort, formula } => {
                if env.use_assert_ground() {
                    Smt::AssertGround {
                        sort,
                        formula: formula.as_ref().into(),
                    }
                } else {
                    Smt::Assert(formula.as_ref().into())
                }
            }
        }
    }
}

impl<'bump> FromEnv<'bump, Declaration<'bump>> for Smt<'bump> {
    fn with_env(env: &Environement<'bump>, dec: Declaration<'bump>) -> Self {
        match dec {
            Declaration::Sort(s) => Self::DeclareSort(s),
            Declaration::FreeFunction(fun) => {
                let (args, out) = if_chain! {
                    if let Some(args) = fun.fast_insort();
                    if let Some(out) = fun.fast_outsort();
                    then {
                        (args, out)
                    } else {
                        panic!("all function defined here have known sort: {}", fun.name())
                    }
                };

                Self::DeclareFun { fun, args, out }
            }
            Declaration::DataTypes(dt) => {
                let (sorts, cons) = dt
                    .into_iter()
                    .map(|dt| {
                        (
                            dt.sort,
                            dt.constructor_destructors
                                .into_iter()
                                .map(|cd| SmtCons {
                                    fun: cd.constructor,
                                    dest: cd.destructor.into_iter().map(Some).collect(),
                                    sorts: cd.constructor.fast_insort().unwrap(),
                                })
                                .collect(),
                        )
                    })
                    .unzip();
                Self::DeclareDatatypes { sorts, cons }
            }
            Declaration::Subterm(sub) => {
                Self::DeclareSubtermRelation(sub.function, sub.comutative_functions)
            }
            Declaration::SortAlias { from, to } => Self::DeclareSortAlias { from, to },
        }
    }
}

impl<'bump> SmtDisplay<'bump> for Smt<'bump> {
    fn into_display(self, env: &impl KnowsRealm) -> impl fmt::Display + 'bump {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }

    fn as_display(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }
}

impl<'bump> FromEnv<'bump, GeneralFile<'bump>> for SmtFile<'bump> {
    fn with_env(
        env: &Environement<'bump>,
        GeneralFile {
            assertions,
            declarations,
        }: GeneralFile<'bump>,
    ) -> Self {
        let declarations = declarations.into_iter().map(|d| Smt::with_env(env, d));
        let assertions = assertions.into_iter().map(|ax| Smt::with_env(env, ax));
        let other = [Smt::CheckSat];

        let content = itertools::chain!(declarations, assertions, other).collect();
        Self { content }
    }
}

impl<'bump> SmtDisplay<'bump> for SmtFile<'bump> {
    fn into_display(self, _: &impl KnowsRealm) -> impl fmt::Display + 'bump {
        ""
    }

    fn as_display(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }
}
