use std::borrow::Cow;

use cryptovampire_macros::smt;
use cryptovampire_smt::{SmtFormula, VarInner};
use egg::VarExposed;
use logic_formula::{Destructed, Formula};

use crate::{LangVar, MSmtFormula};

pub fn var_to_smt(var: &egg::Var) -> VarInner {
    match var.expose() {
        VarExposed::Num(n) => VarInner::Int(n as cryptovampire_smt::uvar),
        VarExposed::Sym(v) => VarInner::Str(Cow::Borrowed(v)),
    }
}

pub fn formula_to_smt(formula: &[LangVar]) -> MSmtFormula {
    use SmtFormula::Var;
    let Destructed { head, args } = formula.destruct();
    match head {
        logic_formula::HeadSk::Var(v) => Var(var_to_smt(&v)),
        logic_formula::HeadSk::Fun(fun) => {
            let args = args.map(formula_to_smt);
            match fun.as_smt_head() {
                Some(head) => SmtFormula::builtin(head, args).expect("wrong number of arguments"),
                None => smt!((fun #args*)),
            }
        }
        logic_formula::HeadSk::Quant(_) => unreachable!(),
    }
}
