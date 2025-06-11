//! This module mostly exists for the macro [rexp] to pull it's functions from.
//! It also contains other miscelenious functions

use crate::{LangVar, terms::Function};
use egg::{Id, PatternAst, RecExpr, Var};
use logic_formula::egg::SimplLang;
use std::borrow::Cow;
use utils::implvec;

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

/// alias for [rexp]
pub type Lang = LangVar;

/// magic ✨
#[macro_export]
macro_rules! rexp {
    ($($t:tt)*) => {
        ::cryptovampire_macros::recexpr!($crate::terms::formula_utils; $($t)*)
    };
}
