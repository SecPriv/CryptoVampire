use std::fmt::Display;

use crate::{Arr};

use super::SortedVar;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum SmtFormula<S, F> {
    Var(u32),
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

impl<S, F> Display for SmtFormula<S, F>
where
    S: Display,
    F: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtFormula::Var(v) => write!(f, "x_{v:}"),
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
                write!(f, "(forall ({}) {formula})", Arr::simple(vars.as_slice()))
            }
            SmtFormula::Exists(vars, formula) => {
                write!(f, "(exists ({}) {formula})", Arr::simple(vars.as_slice()))
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
