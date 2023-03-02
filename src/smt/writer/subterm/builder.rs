use crate::{
    formula::{formula::RichFormula, formula_user::FormulaUser},
    problem::{problem::Problem, step::Step},
    smt::{
        macros::{seq, svar},
        smt::SmtFormula,
    },
};

use super::Subterm;

pub trait Builder<'a> {
    fn analyse(
        self,
        subt: &Subterm<Self>,
        m: &RichFormula,
        s: &Step,
        pbl: &'a Problem,
        f: &'a RichFormula,
    ) -> (Option<RichFormula>, Vec<&'a RichFormula>)
    where
        Self: Sized;
}

impl<'a, F> Builder<'a> for F
where
    F: Fn(
        &Subterm<F>,
        &RichFormula,
        &Step,
        &'a Problem,
        &'a RichFormula,
    ) -> (Option<RichFormula>, Vec<&'a RichFormula>),
{
    fn analyse(
        self,
        subt: &Subterm<Self>,
        m: &RichFormula,
        s: &Step,
        pbl: &'a Problem,
        f: &'a RichFormula,
    ) -> (Option<RichFormula>, Vec<&'a RichFormula>)
    where
        Self: Sized,
    {
        (self)(subt, m, s, pbl, f)
    }
}

pub struct DefaultBuilder();
impl<'a> Builder<'a> for DefaultBuilder {
    fn analyse(
        self,
        subt: &Subterm<Self>,
        m: &RichFormula,
        s: &Step,
        pbl: &'a Problem,
        f: &'a RichFormula,
    ) -> (Option<RichFormula>, Vec<&'a RichFormula>)
    where
        Self: Sized,
    {
        let sort = subt.sort();
        match f {
            RichFormula::Fun(fun, args) => (
                (&fun.get_output_sort() == sort).then(|| pbl.eqf(m.clone(), f.clone())),
                args.iter().collect(),
            ),
            RichFormula::Var(v) if &v.sort == sort => {
                (Some(pbl.eqf(m.clone(), pbl.varf(v.clone()))), vec![])
            }
            _ => (None, vec![]),
        }
    }
}
