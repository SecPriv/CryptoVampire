use std::borrow::Cow;
use std::collections::VecDeque;

use egg::{Analysis, EGraph, ENodeOrVar, Id, Language, PatternAst, RecExpr, Var, VarExposed};
use itertools::{EitherOrBoth, Itertools, izip};
use log::error;
use logic_formula::{Destructed, Formula, HeadSk};
use utils::{econtinue_if, ereturn_if, implvec};

use crate::terms::{FOBinder, Function, RecFOFormula, Sort, Variable, builtin};
use crate::{Lang, LangVar};

/// magic ✨
#[macro_export]
macro_rules! rexp {
  (const $($t:tt)*) => {
      ::cryptovampire_macros::recexpr!( $crate::terms::utils::rexp_macro; const $($t)*)
  };
  ($($t:tt)*) => {
      ::cryptovampire_macros::recexpr!($crate::terms::utils::rexp_macro; $($t)*)
  };
}

pub type MacroExpr = RecFOFormula;
pub type MacroVar = Variable;
pub type MacroFunction = Function;
pub type MacroBinder = FOBinder;

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

pub use crate::fresh;

/// for [rexp]
pub const fn mk_var(var: Variable) -> MacroExpr {
    MacroExpr::mk_var(var)
}

pub fn mk_ands(args: implvec!(MacroExpr)) -> MacroExpr {
    MacroExpr::and(args)
}

pub fn mk_ors(args: implvec!(MacroExpr)) -> MacroExpr {
    MacroExpr::or(args)
}

pub fn mk_eqs(args: implvec!(MacroExpr)) -> MacroExpr {
    todo!()
}

pub fn mk_neqs(args: implvec!(MacroExpr)) -> MacroExpr {
    todo!()
}

/// for [rexp]
pub fn mk_app(head: Function, args: implvec!(MacroExpr)) -> MacroExpr {
    RecFOFormula::App {
        head,
        args: Cow::Owned(args.into_iter().collect_vec()),
    }
}

pub fn mk_const_app(head: Function, args: &'static [MacroExpr]) -> MacroExpr {
    MacroExpr::mk_const_app(head, args)
}

pub const fn mk_const_quantifier(
    head: FOBinder,
    vars: &'static [Variable],
    arg: &'static [MacroExpr],
) -> MacroExpr {
    MacroExpr::Quantifier {
        head,
        vars: Cow::Borrowed(vars),
        arg: Cow::Borrowed(arg),
    }
}

pub fn mk_quantifier(
    head: FOBinder,
    vars: implvec![Variable],
    arg: implvec![MacroExpr],
) -> MacroExpr {
    MacroExpr::bind(head, vars.into_iter().collect(), args)
}

/// Turn an iterator of [LangVar] in a [RecExpr] withtout variable. Returns the
/// first encountered variable as an [Err].
pub fn convert_to_ground_rexp(c: implvec!(LangVar)) -> Result<RecExpr<crate::Lang>, egg::Var> {
    let tmp: PatternAst<crate::Lang> = c.into_iter().collect();
    tmp.try_into()
}
