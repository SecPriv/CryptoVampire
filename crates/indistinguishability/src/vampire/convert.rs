use std::borrow::Cow;

use cryptovampire_macros::smt;
use cryptovampire_smt::{IntoSmt, SmtFormula, VarInner};
use logic_formula::{Destructed, Formula};

use crate::{terms::{RecFOFormula, Variable}, LangVar, MSmtFormula};

pub fn var_to_smt(var: &Variable) -> VarInner {
    VarInner::Str(Cow::Owned(var.to_string()))
}

pub fn formula_to_smt(formula: &[LangVar]) -> MSmtFormula {
    let formula : RecFOFormula = formula.into();
    formula.into_smt()
}