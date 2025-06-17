//! This module mostly exists for the macro [rexp] to pull it's functions from.
//! It also contains other miscelenious functions

use crate::{
    LangVar,
    terms::{Function, Sort},
};
use egg::{ENodeOrVar, Id, PatternAst, RecExpr, Var, VarExposed};
use itertools::{EitherOrBoth, Itertools, izip};
use logic_formula::{Destructed, Formula, HeadSk, egg::SimplLang};
use std::borrow::Cow;
use utils::implvec;

/// magic ✨
#[macro_export]
macro_rules! rexp {
    ($($t:tt)*) => {
        ::cryptovampire_macros::recexpr!($crate::terms::formula_utils; $($t)*)
    };
}

/// for [rexp]
pub static TRUE: Function = super::TRUE.const_clone().unwrap();
/// for [rexp]
pub static FALSE: Function = super::TRUE.const_clone().unwrap();
/// for [rexp]
pub static AND: Function = super::AND.const_clone().unwrap();
/// for [rexp]
pub static OR: Function = super::OR.const_clone().unwrap();
/// for [rexp]
pub static NOT: Function = super::NOT.const_clone().unwrap();
/// for [rexp]
pub static EQ: Function = super::EQ.const_clone().unwrap();
/// for [rexp]
pub static IMPLIES: Function = super::IMPLIES.const_clone().unwrap();

/// for [rexp]
pub const fn mk_var(i: u32) -> LangVar {
    egg::ENodeOrVar::Var(Var::from_u32(i))
}

/// for [rexp]
pub fn mk_app(head: &Function, args: implvec!(u32)) -> LangVar {
    egg::ENodeOrVar::ENode(SimplLang::new(
        head.clone(),
        args.into_iter().map(Id::new_const),
    ))
}

/// Turn an iterator of [LangVar] into a [Cow]ed array
pub fn convert_to_cow(c: implvec!(LangVar)) -> Cow<'static, [LangVar]> {
    c.into_iter().collect()
}

/// Turn an iterator of [LangVar] in a [RecExpr] withtout variable. Returns the
/// first encountered variable as an [Err].
pub fn convert_to_ground_rexp(c: implvec!(LangVar)) -> Result<RecExpr<crate::Lang>, egg::Var> {
    let tmp: PatternAst<crate::Lang> = c.into_iter().collect();
    tmp.try_into()
}

/// **!!! DON'T USE DIRECTLY !!!**
///
/// alias for [rexp]
pub type Lang = LangVar;

pub fn get_sort<'a, F>(f: &'a F) -> Option<Sort>
where
    &'a F: Formula,
    F: ?Sized,
    <&'a F as Formula>::Fun: AsRef<Function>,
{
    match f.head() {
        HeadSk::Var(_) => None,
        HeadSk::Fun(f) => Some(f.as_ref().signature.output),
        HeadSk::Quant(_) => Some(Sort::Bool),
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
                EitherOrBoth::Both(asort, arg) => {
                    type_check(arg) && get_sort(arg).map(|x| x == asort).unwrap_or(true)
                }
                _ => false,
            })
        }
        HeadSk::Quant(_) => izip!(::std::iter::repeat(Sort::Bool), args).all(|(asort, arg)| {
            type_check(arg) && get_sort(arg).map(|x| x == asort).unwrap_or(true)
        }),
    }
}

pub fn offsets_vars<L>(amount: u32, f: &mut [ENodeOrVar<L>]) {
    for e in f {
        if let ENodeOrVar::Var(v) = e
            && let VarExposed::Num(i) = v.expose()
        {
            *v = (i + amount).into()
        }
    }
}
pub fn offsets_owned<L>(amount: u32, f: implvec!(ENodeOrVar<L>)) -> PatternAst<L> {
    let mut f : PatternAst<L> = f.into_iter().collect();
    offsets_vars(amount, &mut f);
    f
}

#[cfg(test)]
mod test {
    use crate::terms::{MITE, NONCE, PROJ_1, TUPLE, formula_utils::type_check};

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
