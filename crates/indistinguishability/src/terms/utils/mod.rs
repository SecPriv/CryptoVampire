use std::borrow::Cow;
use std::collections::VecDeque;

use itertools::{EitherOrBoth, Itertools, izip};
use log::error;
use logic_formula::{Destructed, Formula, HeadSk};

use crate::LangVar;
use crate::terms::{Function, Sort};
use crate::utils::LightClone;

declare_trace!($"formula_utils");

/// This module mostly exists for the macro [rexp] to pull it's functions from.
/// It also contains other miscelenious functions
mod rexp_macro;

pub mod offset;
pub mod pull_from_egraph;

pub fn get_sort<F>(f: F) -> Sort
where
    F: Formula + LightClone,
    <F as Formula>::Fun: AsRef<Function>,
{
    match f.head() {
        HeadSk::Var(_) => Sort::Any,
        HeadSk::Fun(f) => f.as_ref().signature.output,
        HeadSk::Quant(_) => Sort::Bool,
    }
}

pub fn type_check<F>(f: F) -> bool
where
    F: Formula + LightClone,
    <F as Formula>::Fun: AsRef<Function>,
{
    let Destructed { head, args } = f.destruct();
    match head {
        HeadSk::Var(_) => true,
        HeadSk::Fun(fun) => {
            Itertools::zip_longest(fun.as_ref().signature.inputs_iter(), args).all(|x| match x {
                EitherOrBoth::Both(asort, arg) => {
                    get_sort(arg.clone()).unify(asort) && type_check(arg)
                }
                _ => false,
            })
        }
        HeadSk::Quant(_) => izip!(::std::iter::repeat(Sort::Bool), args)
            .all(|(asort, arg)| get_sort(arg.clone()).unify(asort) && type_check(arg)),
    }
}

#[cfg(test)]
mod test {
    use crate::{fresh, rexp};
    use crate::terms::utils::type_check;
    use crate::terms::{FormulaLike, MITE, NONCE, PROJ_1, TUPLE};

    #[test]
    fn type_check_true() {
        let x =
            rexp!((MITE (and true true false) (NONCE #0) (PROJ_1 (TUPLE #1 (NONCE #0))))).to_vec();
        assert!(type_check(x.as_formula()))
    }

    #[test]
    fn type_check_wrong_length() {
        let x = rexp!((MITE (and true true false) (NONCE #0) (PROJ_1 (TUPLE (NONCE #0))))).to_vec();
        assert!(!type_check(x.as_formula()))
    }

    #[test]
    fn type_check_wrong_sort() {
        let v = fresh!(Bitstring);
        let x = rexp!((MITE (and true true false) (and ) (PROJ_1 (TUPLE (NONCE #v)))));
        assert!(!type_check(x.as_formula()))
    }

    fn macro_check1() {
        ::cryptovampire_macros::recexpr!(crate::terms::utils::rexp_macro; const
 (MITE true));

    }
}
