
use std::borrow::Cow;
use std::fmt::{Debug, Display};
use std::ops::{BitAnd, BitOr, Not, Shr};

use anyhow::{Context, bail};
use bon::Builder;
use cryptovampire_smt::{SmtFormula, SmtHead};
use egg::{Analysis, EGraph, Id, Language, Pattern, RecExpr};
use itertools::{Either, Itertools, chain, izip};
use log::{error, trace, warn};
use logic_formula::{Destructed, Formula, HeadSk};
use quarck::CowArc;
use rpds::HashTrieSet;
use rustc_hash::FxHashMap;
use serde::Serialize;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::register_fn::RegisterFn;
use steel::{SteelErr, rerrs};
use steel_derive::Steel;
use utils::{dynamic_iter, econtinue_let, ereturn_if, ereturn_let, implvec, match_eq};

use super::{FOBinder, RecFOFormulaQuant};
use crate::input::Registerable;
use crate::terms::formula::egg::EggLanguage;
use crate::terms::formula::sexpr::SExpr;
use crate::terms::formula::{RecFOFormulaQuantRef, list};
use crate::terms::utils::pull_from_egraph;
use crate::terms::{
    AND, BITE, CONS, EMPTY, EQ, FALSE, Function, IMPLIES, LAMBDA_O, LAMBDA_S, NIL, NOT, OR, Sort,
    TRUE, TUPLE, Variable,
};
use crate::{Lang, LangVar, MSmtFormula, fresh, rexp};
use super::RecFOFormula;

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