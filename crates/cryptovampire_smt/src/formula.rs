use std::{borrow::Cow, fmt::Display};

use itertools::Itertools;
use logic_formula::{Destructed, Formula, HeadSk};
use utils::{ereturn_if, implvec};

use crate::{Arr, VarInner, uvar};

use super::SortedVar;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum SmtFormula<S, F> {
    Var(VarInner),
    Fun(F, Vec<SmtFormula<S, F>>),
    Forall(Vec<SortedVar<S>>, Box<SmtFormula<S, F>>),
    Exists(Vec<SortedVar<S>>, Box<SmtFormula<S, F>>),

    True,
    False,
    And(Vec<SmtFormula<S, F>>),
    Or(Vec<SmtFormula<S, F>>),
    Eq(Vec<SmtFormula<S, F>>),
    Neq(Vec<SmtFormula<S, F>>),
    Not(Box<SmtFormula<S, F>>),
    Implies(Box<SmtFormula<S, F>>, Box<SmtFormula<S, F>>),

    Ite(
        Box<SmtFormula<S, F>>,
        Box<SmtFormula<S, F>>,
        Box<SmtFormula<S, F>>,
    ),

    #[cfg(feature = "cryptovampire")]
    Subterm(F, Box<SmtFormula<S, F>>, Box<SmtFormula<S, F>>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SmtHead {
    True,
    False,
    And,
    Or,
    Eq,
    Neq,
    Not,
    Implies,
    If,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SmtQuantifier<S> {
    Forall(Vec<SortedVar<S>>),
    Exists(Vec<SortedVar<S>>),
}

impl<S, F> Display for SmtFormula<S, F>
where
    S: Display,
    F: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtFormula::Var(v) => write!(f, "{v}"),
            SmtFormula::Fun(fun, smt_formulas) => {
                if smt_formulas.is_empty() {
                    write!(f, "{fun}")
                } else {
                    write!(f, "({fun}")?;
                    for arg in smt_formulas {
                        write!(f, " {arg}")?;
                    }
                    write!(f, ")")
                }
            }
            SmtFormula::Forall(vars, formula) => {
                write!(f, "(forall {} {formula})", Arr::simple(vars.as_slice()))
            }
            SmtFormula::Exists(vars, formula) => {
                write!(f, "(exists {} {formula})", Arr::simple(vars.as_slice()))
            }
            SmtFormula::True => write!(f, "true"),
            SmtFormula::False => write!(f, "false"),
            SmtFormula::And(args) => Arr("and", args.as_slice()).fmt(f),
            SmtFormula::Or(args) => Arr("or", args.as_slice()).fmt(f),
            SmtFormula::Eq(args) => Arr("=", args.as_slice()).fmt(f),
            SmtFormula::Neq(args) => Arr("distinct", args.as_slice()).fmt(f),
            SmtFormula::Not(args) => write!(f, "(not {args})"),
            SmtFormula::Implies(premise, conclusion) => write!(f, "(=> {premise} {conclusion})"),
            SmtFormula::Ite(c, l, r) => write!(f, "(ite {c} {l} {r})"),

            #[cfg(feature = "cryptovampire")]
            SmtFormula::Subterm(fun, a, b) => write!(f, "(subterm {fun} {a} {b})"),
        }
    }
}

impl<S, F> SmtFormula<S, F> {
    pub fn builtin(head: SmtHead, args: implvec!(Self)) -> Result<Self, Vec<Self>> {
        let args: Vec<_> = args.into_iter().collect();
        use SmtFormula::*;
        match head {
            SmtHead::True => {
                ereturn_if!(!args.is_empty(), Err(args));
                Ok(True)
            }
            SmtHead::False => {
                ereturn_if!(!args.is_empty(), Err(args));
                Ok(False)
            }
            SmtHead::And => Ok(And(args)),
            SmtHead::Or => Ok(Or(args)),
            SmtHead::Eq => Ok(Eq(args)),
            SmtHead::Neq => Ok(Neq(args)),
            SmtHead::Not => {
                let [arg] = args.try_into()?;
                Ok(Not(Box::new(arg)))
            }
            SmtHead::Implies => {
                let [premise, conclusion] = args.try_into()?;
                Ok(Implies(Box::new(premise), Box::new(conclusion)))
            }
            SmtHead::If => {
                let [c, l, r] = args.try_into()?;
                Ok(Ite(Box::new(c), Box::new(l), Box::new(r)))
            }
        }
    }

    fn optimise_mut(&mut self)
    where
        Self: Eq,
    {
        match self {
            SmtFormula::Fun(_, args) | SmtFormula::Eq(args) | SmtFormula::Neq(args) => {
                args.iter_mut().for_each(Self::optimise_mut);
            }
            SmtFormula::Forall(_, f) | SmtFormula::Exists(_, f) => {
                f.optimise_mut();
            }
            SmtFormula::And(args) => {
                args.iter_mut().for_each(Self::optimise_mut);
                if args.is_empty() {
                    *self = Self::True
                } else if args.len() == 1 {
                    *self = args.pop().unwrap()
                } else if args.contains(&Self::False) {
                    *self = Self::False
                }
            }
            SmtFormula::Or(args) => {
                args.iter_mut().for_each(Self::optimise_mut);
                if args.is_empty() {
                    *self = Self::False
                } else if args.len() == 1 {
                    *self = args.pop().unwrap()
                } else if args.contains(&Self::False) {
                    *self = Self::True
                }
            }
            SmtFormula::Implies(a, b) => {
                a.optimise_mut();
                if a.as_ref() == &Self::False {
                    *self = Self::True
                } else {
                    b.optimise_mut();
                }
            }
            SmtFormula::Ite(c, l, r) => {
                [c, l, r]
                    .iter_mut()
                    .map(|x| x.as_mut())
                    .for_each(Self::optimise_mut);
            }
            _ => (),
        }
    }

    pub fn optimise(mut self) -> Self
    where
        Self: Eq,
    {
        self.optimise_mut();
        self
    }

    pub fn from_formula<U>(f: U) -> Self
    where
        U: IntoSmt<S, Fun = F>,
    {
        let Destructed { head, args } = f.destruct();
        let args = args.map(Self::from_formula);
        match head {
            HeadSk::Var(v) => Self::Var(U::convert_var(v)),
            HeadSk::Fun(fun) => match U::as_head(&fun) {
                Some(head) => match head {
                    SmtHead::True => Self::True,
                    SmtHead::False => Self::False,
                    SmtHead::And => Self::And(args.collect()),
                    SmtHead::Or => Self::Or(args.collect()),
                    SmtHead::Eq => Self::Eq(args.collect()),
                    SmtHead::Neq => Self::Neq(args.collect()),
                    SmtHead::Not => {
                        let mut args = args;
                        let a = args.next().unwrap();
                        debug_assert!(args.next().is_none());
                        Self::Not(Box::new(a))
                    }
                    SmtHead::Implies => {
                        let (a, b) = args.collect_tuple().unwrap();
                        Self::Implies(Box::new(a), Box::new(b))
                    }
                    SmtHead::If => {
                        let (a, b, c) = args.collect_tuple().unwrap();
                        Self::Ite(Box::new(a), Box::new(b), Box::new(c))
                    }
                },
                None => Self::Fun(fun, args.collect()),
            },
            HeadSk::Quant(binder) => {
                let mut args = args;
                let inner = args.next().unwrap();
                debug_assert!(args.next().is_none());
                match U::convert_quant(binder) {
                    SmtQuantifier::Exists(vars) => Self::Exists(vars, Box::new(inner)),
                    SmtQuantifier::Forall(vars) => Self::Forall(vars, Box::new(inner)),
                }
            }
        }
    }
}

impl<S, F> From<SortedVar<S>> for SmtFormula<S, F> {
    fn from(SortedVar { var, .. }: SortedVar<S>) -> Self {
        SmtFormula::Var(var)
    }
}

impl<S, F> From<uvar> for SmtFormula<S, F> {
    fn from(value: uvar) -> Self {
        SmtFormula::Var(VarInner::Int(value))
    }
}

pub trait IntoSmt<S>: Formula {
    fn convert_var(var: Self::Var) -> VarInner;
    fn convert_quant(quant: Self::Quant) -> SmtQuantifier<S>;
    fn as_head(fun: &Self::Fun) -> Option<SmtHead>;
}
