use std::borrow::Cow;
use std::collections::VecDeque;

use egg::{Analysis, EGraph, ENodeOrVar, Id, Language, PatternAst, RecExpr, Var, VarExposed};
use itertools::{EitherOrBoth, Itertools, izip};
use log::error;
use logic_formula::{Destructed, Formula, HeadSk};
use utils::{econtinue_if, ereturn_if, implvec};

use crate::terms::{Function, Sort, builtin};
use crate::{Lang, LangVar};

/// magic ✨
#[macro_export]
macro_rules! rexp {
  ($($t:tt)*) => {
      ::cryptovampire_macros::recexpr!($crate::terms::utils; $($t)*)
  };
}

/// for [rexp]
pub static TRUE: Function = builtin::TRUE.const_clone().unwrap();
/// for [rexp]
pub static FALSE: Function = builtin::FALSE.const_clone().unwrap();
/// for [rexp]
pub static AND: Function = builtin::AND.const_clone().unwrap();
/// for [rexp]
pub static OR: Function = builtin::OR.const_clone().unwrap();
/// for [rexp]
pub static NOT: Function = builtin::NOT.const_clone().unwrap();
/// for [rexp]
pub static EQ: Function = builtin::EQ.const_clone().unwrap();
/// for [rexp]
pub static IMPLIES: Function = builtin::IMPLIES.const_clone().unwrap();

/// for [rexp]
pub const fn mk_var(i: u32) -> LangVar {
    egg::ENodeOrVar::Var(Var::from_usize(i))
}

/// for [rexp]
pub fn mk_app(head: &Function, args: implvec!(u32)) -> LangVar {
    egg::ENodeOrVar::ENode(crate::Lang::new(
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
pub type RexpLang = LangVar;
