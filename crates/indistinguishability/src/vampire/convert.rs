use std::borrow::Cow;

use cryptovampire_macros::smt;
use cryptovampire_smt::{IntoSmt, SmtFormula, VarInner};
use egg::VarExposed;
use logic_formula::{Destructed, Formula};

use crate::{terms::RecFOFormula, LangVar, MSmtFormula};

pub fn var_to_smt(var: &egg::Var) -> VarInner {
    match var.expose() {
        VarExposed::Num(n) => VarInner::Int(n as cryptovampire_smt::uvar),
        VarExposed::Sym(v) => VarInner::Str(Cow::Borrowed(v)),
    }
}

pub fn formula_to_smt(formula: &[LangVar]) -> MSmtFormula {
    let formula : RecFOFormula = formula.into();
    formula.into_smt()
}
