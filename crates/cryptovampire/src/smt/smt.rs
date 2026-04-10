use std::borrow::Cow;
use std::fmt;

use cryptovampire_smt::SortedVar;
use if_chain::if_chain;
use quarck::CowArc;

use self::display::{SmtDisplayer, SmtEnv};
use crate::environement::environement::Environement;
use crate::environement::traits::{KnowsRealm, Realm};
use crate::formula::file_descriptior::GeneralFile;
use crate::formula::file_descriptior::axioms::{Axiom, Rewrite, RewriteKind};
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::RichFormula;
use crate::formula::function::inner::booleans::{Booleans, Connective};
use crate::formula::function::{Function, InnerFunction};
use crate::formula::quantifier::Quantifier;
use crate::formula::sort::Sort;
use crate::formula::variable::Variable;
use crate::{FromEnv, SubtermKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SmtParams<'bump>(std::marker::PhantomData<&'bump ()>);

impl<'bump> cryptovampire_smt::SmtParam for SmtParams<'bump> {
    type Function = Function<'bump>;
    type Sort = Sort<'bump>;
    type SVar = SortedVariable<'bump>;
}

pub type SmtFile<'bump> = cryptovampire_smt::SmtFile<'bump, SmtParams<'bump>>;
pub type Smt<'bump> = cryptovampire_smt::Smt<'bump, SmtParams<'bump>>;
pub type SmtFormula<'bump> = cryptovampire_smt::SmtFormula<'bump, SmtParams<'bump>>;
pub type SmtCons<'bump> = cryptovampire_smt::SmtCons<SmtParams<'bump>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SortedVariable<'bump> {
    pub var: Variable<'bump>,
}

impl<'bump> SortedVar for SortedVariable<'bump> {
    type Sort = Sort<'bump>;

    fn sort_ref(&self) -> Cow<'_, Self::Sort> {
        Cow::Borrowed(&self.var.sort)
    }

    fn mk(sort: Self::Sort) -> Self {
        SortedVariable {
            var: Variable::new(0, sort),
        }
    }
}

impl<'bump> fmt::Display for SortedVariable<'bump> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.var)
    }
}

mod display;

fn vars_to_sorted_vars<'bump>(vars: &[Variable<'bump>]) -> CowArc<'bump, [SortedVariable<'bump>]> {
    vars.iter()
        .map(|v| SortedVariable { var: *v })
        .collect::<Vec<_>>()
        .into()
}

fn rich_to_smt_formula<'a, 'bump>(formula: &'a RichFormula<'bump>) -> SmtFormula<'bump> {
    match formula {
        RichFormula::Var(v) => SmtFormula::Var(SortedVariable { var: *v }),
        RichFormula::Quantifier(q, arg) => {
            let vars = vars_to_sorted_vars(match q {
                Quantifier::Exists { variables } | Quantifier::Forall { variables } => variables,
            });
            let inner = rich_to_smt_formula(arg);
            match q {
                Quantifier::Exists { .. } => {
                    SmtFormula::Exists(vars, CowArc::Owned(std::sync::Arc::new(inner)))
                }
                Quantifier::Forall { .. } => {
                    SmtFormula::Forall(vars, CowArc::Owned(std::sync::Arc::new(inner)))
                }
            }
        }
        RichFormula::Fun(f, args) => {
            let args_vec: Vec<_> = args.iter().map(|a| rich_to_smt_formula(a)).collect();
            let args_cow: CowArc<'_, [SmtFormula<'bump>]> = args_vec.into();

            match f.as_inner() {
                InnerFunction::TermAlgebra(_)
                | InnerFunction::Step(_)
                | InnerFunction::Predicate(_)
                | InnerFunction::Tmp(_)
                | InnerFunction::Skolem(_)
                | InnerFunction::Name(_)
                | InnerFunction::EvaluatedFun(_)
                | InnerFunction::Evaluate(_) => SmtFormula::Fun(*f, args_cow),
                InnerFunction::Subterm(subterm) => match subterm.kind() {
                    SubtermKind::Regular(_) => SmtFormula::Fun(*f, args_cow),
                    SubtermKind::Vampire(_) => {
                        let slice = args_cow.as_ref();
                        let [a, b] = slice.to_vec().try_into().unwrap();
                        SmtFormula::Subterm(*f, CowArc::Owned(std::sync::Arc::new([a, b])))
                    }
                },
                InnerFunction::IfThenElse(_) => {
                    let slice = args_cow.as_ref();
                    let [c, l, r] = slice.to_vec().try_into().unwrap();
                    SmtFormula::Ite(CowArc::Owned(std::sync::Arc::new([c, l, r])))
                }
                InnerFunction::Bool(c) => match c {
                    Booleans::Equality(_) => SmtFormula::Eq(args_cow),
                    Booleans::Connective(c) => match c {
                        Connective::True => SmtFormula::True,
                        Connective::False => SmtFormula::False,
                        Connective::And => SmtFormula::And(args_cow),
                        Connective::Or => SmtFormula::Or(args_cow),
                        Connective::Not => {
                            let slice = args_cow.as_ref();
                            let [arg] = slice.to_vec().try_into().unwrap();
                            SmtFormula::Not(CowArc::Owned(std::sync::Arc::new(arg)))
                        }
                        Connective::Implies => {
                            let slice = args_cow.as_ref();
                            let [a, b] = slice.to_vec().try_into().unwrap();
                            SmtFormula::Implies(CowArc::Owned(std::sync::Arc::new([a, b])))
                        }
                    },
                },
            }
        }
    }
}

impl<'a, 'bump> From<&'a RichFormula<'bump>> for SmtFormula<'bump> {
    fn from(formula: &'a RichFormula<'bump>) -> Self {
        rich_to_smt_formula(formula)
    }
}

pub(crate) trait SmtDisplay<'bump>: Sized {
    fn into_display(self, env: &impl KnowsRealm) -> impl fmt::Display + 'bump;
    fn as_display(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_;
    fn prop<D, T>(&self, disp: SmtDisplayer<D, T>) -> SmtDisplayer<D, &Self> {
        disp.propagate(self)
    }
    fn default_display(&self) -> impl fmt::Display + '_ {
        self.as_display(&Realm::Symbolic)
    }
}

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
                    Smt::Assert(SmtFormula::Not(f.into()))
                }
            }
            Axiom::Rewrite { rewrite } => {
                let Rewrite {
                    kind,
                    vars,
                    pre,
                    post,
                } = *rewrite;
                let pre: SmtFormula<'bump> = pre.as_ref().into();
                let post: SmtFormula<'bump> = post.as_ref().into();
                if env.no_rewrite() {
                    let formula = SmtFormula::Eq(vec![pre, post].into());
                    Smt::Assert(SmtFormula::Forall(
                        vars_to_sorted_vars(&vars),
                        formula.into(),
                    ))
                } else {
                    Smt::DeclareRewrite {
                        rewrite_fun: kind,
                        vars: vars_to_sorted_vars(&vars).to_vec(),
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
    fn with_env(_env: &Environement<'bump>, dec: Declaration<'bump>) -> Self {
        match dec {
            Declaration::Sort(s) => Self::DeclareSort(s),
            Declaration::FreeFunction(fun) => {
                let (args, out) = if_chain! {
                    if let Some(args) = fun.fast_insort();
                    if let Some(out) = fun.fast_outsort();
                    then { (args, out) }
                    else { panic!("all function defined here have known sort: {}", fun.name()) }
                };
                Self::DeclareFun {
                    fun,
                    args: args.into(),
                    out,
                }
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
                Self::DeclareSubtermRelation(sub.function, sub.comutative_functions.into())
            }
            Declaration::SortAlias { from, to } => Self::DeclareSortAlias { from: to, to: from },
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
