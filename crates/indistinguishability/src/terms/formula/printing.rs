use super::RecFOFormula;
use crate::terms::Variable;
use crate::terms::formula::sexpr::SExpr;
use itertools::chain;
use std::fmt::{Display, Debug};

impl Display for RecFOFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        super::sexpr::SExpr::from(self).fmt(f)
    }
}

impl Debug for RecFOFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        #[cfg(feature = "verbose")]
        {
            match self {
                Self::Quantifier { head, vars, arg } => f
                    .debug_struct("Quantifier")
                    .field("head", head)
                    .field("vars", vars)
                    .field("arg", arg)
                    .finish(),
                Self::App { head, args } => f
                    .debug_struct("App")
                    .field("head", head)
                    .field("args", args)
                    .finish(),
                Self::Var(arg0) => f.debug_tuple("Var").field(arg0).finish(),
            }
        }

        #[cfg(not(feature = "verbose"))]
        {
            Display::fmt(&self, f)
        }
    }
}

static FULL_VARS: bool = false;
impl<'a> From<&'a RecFOFormula> for SExpr<'a> {
    fn from(value: &'a RecFOFormula) -> Self {
        use SExpr::*;
        match value {
            RecFOFormula::Quantifier { head, vars, arg } => Group(vec![
                Atom(head),
                Group(vars.iter().map(|x| mk_var_sexpr(x)).collect()),
                Group(arg.iter().map(|x| Atom(x)).collect()),
            ]),
            RecFOFormula::App { head, args } => {
                Group(chain![[Atom(head)], args.iter().map(|x| Atom(x)),].collect())
            }
            RecFOFormula::Var(variable) => mk_var_sexpr(variable),
        }
    }
}

#[inline]
fn mk_var_sexpr<'a>(v: &'a Variable) -> SExpr<'a> {
    use SExpr::*;
    if FULL_VARS { Atom(v) } else { AtomDebug(v) }
}
