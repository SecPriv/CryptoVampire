
use std::borrow::Cow;
use std::collections::VecDeque;

use egg::{};
use itertools::{EitherOrBoth, Itertools, izip};
use log::error;
use logic_formula::egg::SimplLang;
use logic_formula::{Destructed, Formula, HeadSk};
use utils::{};

use crate::terms::{Function, Sort};
use crate::{LangVar};

declare_trace!($"formula_utils");

/// This module mostly exists for the macro [rexp] to pull it's functions from.
/// It also contains other miscelenious functions
mod rexp_helpers;
pub use rexp_helpers::*;

pub mod offset;
pub mod pull_from_egraph;

pub fn get_sort<'a, F>(f: &'a F) -> Sort
where
    &'a F: Formula,
    F: ?Sized,
    <&'a F as Formula>::Fun: AsRef<Function>,
{
    match f.head() {
        HeadSk::Var(_) => Sort::Any,
        HeadSk::Fun(f) => f.as_ref().signature.output,
        HeadSk::Quant(_) => Sort::Bool,
    }
}

pub fn type_check<'a, F>(f: &'a F) -> bool
where
    &'a F: Formula,
    F: ?Sized,
    <&'a F as Formula>::Fun: AsRef<Function>,
{
    let Destructed { head, args } = f.destruct();
    match head {
        HeadSk::Var(_) => true,
        HeadSk::Fun(fun) => {
            Itertools::zip_longest(fun.as_ref().signature.inputs_iter(), args).all(|x| match x {
                EitherOrBoth::Both(asort, arg) => get_sort(arg).unify(asort) && type_check(arg),
                _ => false,
            })
        }
        HeadSk::Quant(_) => izip!(::std::iter::repeat(Sort::Bool), args)
            .all(|(asort, arg)| get_sort(arg).unify(asort) && type_check(arg)),
    }
}

#[cfg(test)]
mod test {
    use crate::rexp;
    use crate::terms::utils::type_check;
    use crate::terms::{MITE, NONCE, PROJ_1, TUPLE};

    #[test]
    fn type_check_true() {
        let x =
            rexp!((MITE (and true true false) (NONCE #0) (PROJ_1 (TUPLE #1 (NONCE #0))))).to_vec();
        assert!(type_check(x.as_slice()))
    }

    #[test]
    fn type_check_wrong_length() {
        let x = rexp!((MITE (and true true false) (NONCE #0) (PROJ_1 (TUPLE (NONCE #0))))).to_vec();
        assert!(!type_check(x.as_slice()))
    }

    #[test]
    fn type_check_wrong_sort() {
        let x = rexp!((MITE (and true true false) (and ) (PROJ_1 (TUPLE (NONCE #0))))).to_vec();
        assert!(!type_check(x.as_slice()))
    }
}
