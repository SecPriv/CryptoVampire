use crate::{
    formula::{formula::RichFormula, formula_user::FormulaUser},
    problem::{problem::Problem, step::Step},
};

use super::Subterm;

pub trait Builder {
    fn analyse<'a>(
        &self,
        subt: &Subterm<Self>,
        m: &RichFormula,
        s: Option<&Step>,
        pbl: &'a Problem,
        f: &'a RichFormula,
    ) -> (Option<RichFormula>, Vec<&'a RichFormula>)
    where
        Self: Sized;
}

// impl<'a, F> Builder<'a> for F
// where
//     F: Fn(
//         &Subterm<F>,
//         &RichFormula,
//         Option<&Step>,
//         &'a Problem,
//         &'a RichFormula,
//     ) -> (Option<RichFormula>, Vec<&'a RichFormula>),
// {
//     fn analyse(
//         &self,
//         subt: &Subterm<Self>,
//         m: &RichFormula,
//         s: Option<&Step>,
//         pbl: &'a Problem,
//         f: &'a RichFormula,
//     ) -> (Option<RichFormula>, Vec<&'a RichFormula>)
//     where
//         Self: Sized,
//     {
//         (self)(subt, m, s, pbl, f)
//     }
// }

// pub struct FBuilder<F>(F);
// impl<'a, F> Builder<'a> for FBuilder<F>
// where
//     F: Fn(
//         &RichFormula,
//         &'a Problem,
//         &'a RichFormula,
//     ) -> (Option<RichFormula>, Vec<&'a RichFormula>),
// {
//     fn analyse(
//         &self,
//         subt: &Subterm<Self>,
//         m: &RichFormula,
//         s: Option<&Step>,
//         pbl: &'a Problem,
//         f: &'a RichFormula,
//     ) -> (Option<RichFormula>, Vec<&'a RichFormula>)
//     where
//         Self: Sized,
//     {
//         (self.0)(m, pbl, f)
//     }
// }

// impl<'a, F> FBuilder<F>
// where
//     F: Fn(
//         &RichFormula,
//         &'a Problem,
//         &'a RichFormula,
//     ) -> (Option<RichFormula>, Vec<&'a RichFormula>),
// {
//     pub fn new(f: F) -> Self {
//         FBuilder(f)
//     }
// }

pub struct DefaultBuilder();
impl Builder for DefaultBuilder {
    fn analyse<'a>(
        &self,
        subt: &Subterm<Self>,
        m: &RichFormula,
        _s: Option<&Step>,
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
