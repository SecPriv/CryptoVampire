use std::{
    borrow::Cow,
    ops::{BitAnd, BitOr, Not, Shr},
    rc::Rc,
};

use cryptovampire_smt::{IntoSmt, SmtFormula, SmtQuantifier, SortedVar, VarInner};
use egg::{ENodeOrVar, PatternAst, RecExpr, Var};
use itertools::{Itertools, izip};
use logic_formula::{Destructed, Formula, Head, HeadSk};
use utils::{
    dynamic_iter, ereturn_let, implvec, match_eq,
    quack::{CowArc, CowRc},
    vecref::VecRef,
};

use crate::{
    Lang, LangVar,
    terms::{
        AND, BITE, EQ, FALSE, Function, IMPLIES, NOT, OR, Sort, TRUE, convert_smt_var,
        unification::Subst,
    },
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RecFOFormula {
    Binder {
        head: FOBinder,
        vars: Vec<Var>,
        sorts: Vec<Sort>,
        arg: Box<RecFOFormula>,
    },
    App {
        head: Function,
        args: Vec<RecFOFormula>,
    },
    Var(Var),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum FOBinder {
    Forall,
    Exists,
}

pub type FOSubst = Subst<Var, RecFOFormula>;

impl RecFOFormula {
    pub fn bind(kind: FOBinder, vars: Vec<Var>, sorts: Vec<Sort>, arg: RecFOFormula) -> Self {
        Self::Binder {
            head: kind,
            vars,
            sorts,
            arg: Box::new(arg),
        }
    }

    pub fn app(fun: Function, args: Vec<Self>) -> Self {
        Self::App { head: fun, args }
    }

    pub fn fold(
        fun: &Function,
        args: implvec!(Self),
        default: Option<Self>,
        give_up_on_one: bool,
    ) -> Self {
        let mut args = args.into_iter();
        let a = args.next().unwrap_or_else(|| default.unwrap());
        let Some(b) = args.next() else {
            if give_up_on_one {
                panic!("giving up as requested")
            } else {
                return a;
            }
        };

        args.fold(Self::app(fun.clone(), vec![a, b]), |acc, x| {
            Self::app(fun.clone(), vec![acc, x])
        })
    }

    /// Tries to evaluate an expression, return [None] if it can't
    pub fn try_evaluate(&self) -> Option<bool> {
        match self {
            RecFOFormula::App { head, args } => {
                match_eq! { head => {
                    TRUE => {Some(true)},
                    FALSE => {Some(false)},
                    NOT => {Some(!args[0].try_evaluate()?)},
                    AND => {
                        let l = args[0].try_evaluate();
                        let r = args[1].try_evaluate();
                        if l == Some(false) || r == Some(false) {
                            Some(false)
                        } else {
                            Some(l? && r?)
                        }
                    },
                    OR => {
                        let l = args[0].try_evaluate();
                        let r = args[1].try_evaluate();
                        if l == Some(true) || r == Some(true) {
                            Some(true)
                        } else {
                            Some(l? || r?)
                        }
                    },
                    IMPLIES => {
                        let l = args[0].try_evaluate();
                        let r = args[1].try_evaluate();
                        if l == Some(false) || r == Some(true) {
                            Some(true)
                        } else {
                            Some((!l?) || r?)
                        }
                    },
                    _ => {None}
                }}
            }
            RecFOFormula::Binder { head, arg, .. } => arg.try_evaluate(),
            _ => None,
        }
    }

    // =========================================================
    // ================== specific builders ====================
    // =========================================================

    #[allow(non_snake_case)]
    pub fn True() -> Self {
        Self::app(TRUE.clone(), vec![])
    }

    #[allow(non_snake_case)]
    pub fn False() -> Self {
        Self::app(FALSE.clone(), vec![])
    }

    pub fn and(args: implvec!(Self)) -> Self {
        Self::fold(&AND, args, Some(Self::True()), false)
    }

    pub fn or(args: implvec!(Self)) -> Self {
        Self::fold(&OR, args, Some(Self::False()), false)
    }
}

impl From<&[LangVar]> for RecFOFormula {
    fn from(v: &[LangVar]) -> Self {
        let Destructed { head, args } = v.destruct();
        match head {
            HeadSk::Var(v) => Self::Var(v),
            HeadSk::Fun(head) => Self::App {
                head,
                args: args.map_into().collect(),
            },
            HeadSk::Quant(_) => unreachable!(),
        }
    }
}

impl From<bool> for RecFOFormula {
    fn from(value: bool) -> Self {
        match value {
            true => Self::True(),
            false => Self::False(),
        }
    }
}

impl Default for RecFOFormula {
    fn default() -> Self {
        Self::App {
            head: TRUE.clone(),
            args: vec![],
        }
    }
}

impl Formula for RecFOFormula {
    type Var = egg::Var;

    type Fun = Function;

    type Quant = (FOBinder, Vec<Var>, Vec<Sort>);

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            RecFOFormula::Binder {
                head,
                vars,
                sorts,
                arg,
            } => Destructed {
                head: HeadSk::Quant((head, vars, sorts)),
                args: MIter::One([*arg].into_iter()),
            },
            RecFOFormula::App { head, args } => Destructed {
                head: HeadSk::Fun(head.clone()),
                args: MIter::Many(args.into_iter()),
            },
            RecFOFormula::Var(var) => Destructed {
                head: HeadSk::Var(var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}

impl<'b> Formula for &'b RecFOFormula {
    type Var = egg::Var;

    type Fun = &'b Function;

    type Quant = (FOBinder, &'b [Var], &'b [Sort]);

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            RecFOFormula::Binder {
                head,
                vars,
                sorts,
                arg,
            } => Destructed {
                head: HeadSk::Quant((*head, vars, sorts)),
                args: MIter::One([arg.as_ref()].into_iter()),
            },
            RecFOFormula::App { head, args } => Destructed {
                head: HeadSk::Fun(head),
                args: MIter::Many(args.iter()),
            },
            RecFOFormula::Var(var) => Destructed {
                head: HeadSk::Var(*var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}

impl From<SmtFormula<Sort, Function>> for RecFOFormula {
    fn from(value: SmtFormula<Sort, Function>) -> Self {
        match value {
            SmtFormula::Var(var) => Self::Var(convert_smt_var(var)),
            SmtFormula::Fun(fun, args) => RecFOFormula::App {
                head: fun,
                args: args.into_iter().map_into().collect(),
            },
            SmtFormula::Forall(vars, formula) => {
                let (vars, sorts) = vars
                    .into_iter()
                    .map(|SortedVar { var, sort }| (convert_smt_var(var), sort))
                    .unzip();
                let arg = Box::new(Self::from(*formula));
                Self::Binder {
                    head: FOBinder::Forall,
                    vars,
                    sorts,
                    arg,
                }
            }
            SmtFormula::Exists(vars, formula) => {
                let (vars, sorts) = vars
                    .into_iter()
                    .map(|SortedVar { var, sort }| (convert_smt_var(var), sort))
                    .unzip();
                let arg = Box::new(Self::from(*formula));
                Self::Binder {
                    head: FOBinder::Exists,
                    vars,
                    sorts,
                    arg,
                }
            }
            SmtFormula::True => Self::app(TRUE.clone(), vec![]),
            SmtFormula::False => Self::app(FALSE.clone(), vec![]),
            SmtFormula::And(args) => Self::fold(&AND, args.into_iter().map_into(), None, false),
            SmtFormula::Or(args) => Self::fold(&OR, args.into_iter().map_into(), None, false),
            SmtFormula::Eq(args) => Self::fold(&EQ, args.into_iter().map_into(), None, true),
            SmtFormula::Neq(args) => !Self::fold(&EQ, args.into_iter().map_into(), None, true),
            SmtFormula::Not(arg) => !Self::from(*arg),
            SmtFormula::Implies(a, b) => Self::from(*a) >> Self::from(*b),
            SmtFormula::Ite(c, l, r) => {
                Self::app(BITE.clone(), [c, l, r].map(|x| Self::from(*x)).into())
            }
            _ => unimplemented!(),
        }
    }
}

impl Not for RecFOFormula {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::app(NOT.clone(), vec![self])
    }
}

impl BitAnd for RecFOFormula {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::app(AND.clone(), vec![self, rhs])
    }
}

impl BitOr for RecFOFormula {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::app(OR.clone(), vec![self, rhs])
    }
}

impl Shr for RecFOFormula {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        Self::app(IMPLIES.clone(), vec![self, rhs])
    }
}

impl IntoSmt<Sort> for RecFOFormula {
    fn convert_var(var: egg::Var) -> VarInner {
        match var.expose() {
            egg::VarExposed::Sym(s) => VarInner::Str(s.into()),
            egg::VarExposed::Num(n) => VarInner::Int(n),
        }
    }

    fn convert_quant((bind, vars, sorts): Self::Quant) -> SmtQuantifier<Sort> {
        let vars = izip!(vars, sorts)
            .map(|(var, sort)| SortedVar {
                var: Self::convert_var(var),
                sort,
            })
            .collect_vec();
        match bind {
            FOBinder::Forall => SmtQuantifier::Forall(vars),
            FOBinder::Exists => SmtQuantifier::Exists(vars),
        }
    }

    fn as_head(fun: &Self::Fun) -> Option<cryptovampire_smt::SmtHead> {
        fun.as_smt_head()
    }
}

impl FOBinder {
    /// The value taken by the quantifier on an empty set
    pub fn on_empty(&self) -> bool {
        match self {
            FOBinder::Forall => true,
            FOBinder::Exists => false,
        }
    }
}
