use std::borrow::Cow;

use egg::{Id, PatternAst, RecExpr, Var};
use itertools::Itertools;
use logic_formula::egg::SimplLang;
use utils::implvec;

use crate::{LangVar, terms::Function};

pub static TRUE: Function = super::TRUE.const_clone().unwrap();
pub static FALSE: Function = super::TRUE.const_clone().unwrap();
pub static AND: Function = super::AND.const_clone().unwrap();
pub static OR: Function = super::OR.const_clone().unwrap();
pub static NOT: Function = super::NOT.const_clone().unwrap();
pub static EQ: Function = super::EQ.const_clone().unwrap();
pub static IMPLIES: Function = super::IMPLIES.const_clone().unwrap();

pub const fn mk_var(i: u32) -> LangVar {
    egg::ENodeOrVar::Var(Var::from_u32(i))
}

pub fn mk_app(head: &Function, args: implvec!(u32)) -> LangVar {
    egg::ENodeOrVar::ENode(SimplLang::new(
        head.clone(),
        args.into_iter().map(Id::new_const),
    ))
}

pub fn convert_to_cow(c: implvec!(LangVar)) -> Cow<'static, [LangVar]> {
    c.into_iter().collect()
}

pub fn convert_to_ground_rexp(c: implvec!(LangVar)) -> Result<RecExpr<crate::Lang>, egg::Var> {
    let tmp: PatternAst<crate::Lang> = c.into_iter().collect();
    tmp.try_into()
}

pub type Lang = LangVar;

#[macro_export]
macro_rules! rexp {
    ($($t:tt)*) => {
        ::cryptovampire_macros::recexpr!($crate::terms::formula_utils; $($t)*)
    };
}
