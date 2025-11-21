use egg::{PatternAst, RecExpr};
use itertools::{Itertools, izip};
use quarck::CowArc;
use utils::implvec;

use crate::LangVar;
use crate::terms::{FOBinder, Formula, Function, Variable, builtin};

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

#[macro_export]
macro_rules! smt {
    ($($t:tt)*) => {
        ::cryptovampire_macros::smt!($crate::terms::utils::rexp_macro; $($t)*)
    };
}

#[macro_export]
macro_rules! vec_smt {
    (% $($t:tt)*) => {
        ::cryptovampire_macros::vec_smt2!($crate::terms::utils::rexp_macro; $($t)*)
    };
    ($($t:tt)*) => {
        ::cryptovampire_macros::vec_smt!($crate::terms::utils::rexp_macro; $($t)*)
    };
}

pub type SmtFormula = crate::MSmtFormula;
pub type Smt = crate::MSmt;

pub type MacroExpr = Formula;
pub type MacroVar = Variable;
pub type MacroFunction = Function;
pub type MacroBinder = FOBinder;

/// for [rexp]
pub static TRUE: Function = builtin::TRUE.const_clone();
/// for [rexp]
pub static FALSE: Function = builtin::FALSE.const_clone();
/// for [rexp]
pub static AND: Function = builtin::AND.const_clone();
/// for [rexp]
pub static OR: Function = builtin::OR.const_clone();
/// for [rexp]
pub static NOT: Function = builtin::NOT.const_clone();
/// for [rexp]
pub static EQ: Function = builtin::EQ.const_clone();
/// for [rexp]
pub static IMPLIES: Function = builtin::IMPLIES.const_clone();

pub use crate::fresh;

/// for [rexp]
pub const fn mk_var(var: Variable) -> MacroExpr {
    MacroExpr::mk_var(var)
}

/// for [rexp]
pub const fn mk_var_from_ref(var: &Variable) -> MacroExpr {
    MacroExpr::mk_var(var.const_clone())
}

pub fn mk_ands(args: implvec!(MacroExpr)) -> MacroExpr {
    MacroExpr::and(args)
}

pub fn mk_ors(args: implvec!(MacroExpr)) -> MacroExpr {
    MacroExpr::or(args)
}

pub fn mk_eqs(args: implvec!(MacroExpr)) -> MacroExpr {
    let args = args.into_iter().collect_vec();
    MacroExpr::and(
        args.iter()
            .cloned()
            .tuple_combinations()
            .map(|(a, b)| Formula::App {
                head: EQ.const_clone(),
                args: mk_cowarc![a, b],
            }),
    )
}

pub fn mk_neqs(args: implvec!(MacroExpr)) -> MacroExpr {
    let args = args.into_iter().collect_vec();
    MacroExpr::and(
        args.iter()
            .cloned()
            .tuple_combinations()
            .map(|(a, b)| !Formula::App {
                head: EQ.const_clone(),
                args: mk_cowarc![a, b],
            }),
    )
}

/// for [rexp]
#[allow(private_bounds)]
#[track_caller]
pub fn mk_app<T: FunctionRef>(head: T, args: implvec!(MacroExpr)) -> MacroExpr {
    let args = CowArc::Owned(args.into_iter().collect());
    let head = head.to_function();

    #[cfg(debug_assertions)]
    for (s, arg) in izip!(head.args_sorts(), args.iter()) {
        if !arg.has_sort(s) {
            let ret = Formula::App {
                head: head.clone(),
                args: args.clone(),
            };
            panic!("typing error, expected sort {s} for {arg}\n\nin {ret}")
        }
    }

    debug_assert_eq!(
        head.clone().arity(),
        args.clone().len(),
        "arity mismatch with {}",
        Formula::App { head, args }
    );

    Formula::App { head, args }
}

#[track_caller]
pub const fn mk_const_app(head: Function, args: &'static [MacroExpr]) -> MacroExpr {
    MacroExpr::mk_const_app(head, args)
}

#[track_caller]
pub const fn mk_const_quantifier(
    head: FOBinder,
    vars: &'static [Variable],
    arg: &'static [MacroExpr],
) -> MacroExpr {
    MacroExpr::Quantifier {
        head,
        vars: CowArc::Borrowed(vars),
        arg: CowArc::Borrowed(arg),
    }
}

#[track_caller]
pub fn mk_quantifier(
    head: FOBinder,
    vars: implvec![Variable],
    args: implvec![MacroExpr],
) -> MacroExpr {
    MacroExpr::bind(head, vars.into_iter().collect(), args)
}

/// Turn an iterator of [LangVar] in a [RecExpr] withtout variable. Returns the
/// first encountered variable as an [Err].
pub fn convert_to_ground_rexp(c: implvec!(LangVar)) -> Result<RecExpr<crate::Lang>, egg::Var> {
    let tmp: PatternAst<crate::Lang> = c.into_iter().collect();
    tmp.try_into()
}

pub(crate) trait FunctionRef {
    fn to_function(&self) -> Function;
}

impl FunctionRef for Function {
    fn to_function(&self) -> Function {
        self.clone()
    }
}

impl FunctionRef for &Function {
    fn to_function(&self) -> Function {
        (*self).clone()
    }
}
