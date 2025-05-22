use logic_formula::{Destructed, Formula};

use super::MSmtFormula;

use crate::LangVar;

use std::borrow::Cow;

use egg::VarExposed;

use cryptovampire_smt::{SmtFormula, VarInner};


pub fn var_to_smt(var: &egg::Var) -> VarInner {
    match var.expose() {
        VarExposed::Num(n) => VarInner::Int(n),
        VarExposed::Sym(v) => VarInner::Str(Cow::Borrowed(v)),
    }
}

pub fn formula_to_smt(formula: &[LangVar]) -> MSmtFormula {
    use SmtFormula::*;
    let Destructed { head, args } = formula.destruct();
    match head {
        logic_formula::HeadSk::Var(v) => Var(var_to_smt(&v)),
        logic_formula::HeadSk::Fun(fun) => {
            let args = args.map(formula_to_smt);
            match fun.as_smt_head() {
                Some(head) => SmtFormula::builtin(head, args).expect("wrong number of arguments"),
                None => SmtFormula::Fun(fun, args.collect()),
            }
        }
        logic_formula::HeadSk::Quant(_) => unreachable!(),
    }
}
