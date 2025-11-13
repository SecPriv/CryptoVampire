
use std::borrow::Cow;
use std::fmt::{Debug, Display};
use std::ops::{BitAnd, BitOr, Not, Shr};

use anyhow::{Context, bail};
use bon::Builder;
use cryptovampire_smt::{SmtFormula, SmtHead};
use egg::{Analysis, EGraph, Id, Language, Pattern, RecExpr};
use itertools::{Either, Itertools, chain, izip};
use log::{error, trace, warn};
use logic_formula::{Destructed, Formula, HeadSk};
use quarck::CowArc;
use rpds::HashTrieSet;
use rustc_hash::FxHashMap;
use serde::Serialize;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::register_fn::RegisterFn;
use steel::{SteelErr, rerrs};
use steel_derive::Steel;
use utils::{dynamic_iter, econtinue_let, ereturn_if, ereturn_let, implvec, match_eq};

use super::{FOBinder, RecFOFormulaQuant};
use crate::input::Registerable;
use crate::terms::formula::egg::EggLanguage;
use crate::terms::formula::sexpr::SExpr;
use crate::terms::formula::{RecFOFormulaQuantRef, list};
use crate::terms::utils::pull_from_egraph;
use crate::terms::{
    AND, BITE, CONS, EMPTY, EQ, FALSE, Function, IMPLIES, LAMBDA_O, LAMBDA_S, NIL, NOT, OR, Sort,
    TRUE, TUPLE, Variable,
};
use crate::{Lang, LangVar, MSmtFormula, fresh, rexp};
use super::RecFOFormula;

// =========================================================
// ================== specific builders ====================
// =========================================================
impl RecFOFormula {
    pub fn bind(kind: FOBinder, vars: Vec<Variable>, args: implvec!(RecFOFormula)) -> Self {
        assert!(vars.iter().all(Variable::has_sort));
        Self::Quantifier {
            head: kind,
            vars: vars.into(),
            arg: args.into_iter().collect(),
        }
    }

    pub fn app(fun: Function, args: Vec<Self>) -> Self {
        Self::App {
            head: fun,
            args: args.into(),
        }
    }

    pub fn fold(
        fun: &Function,
        args: implvec!(Self),
        default: Option<Self>,
        give_up_on_one: bool,
    ) -> Self {
        let mut args = args.into_iter();
        let a = args.next().unwrap_or_else(|| default.unwrap());
        let Some(b) = args.next() else {
            if give_up_on_one {
                panic!("giving up as requested")
            } else {
                return a;
            }
        };

        args.fold(Self::app(fun.clone(), vec![a, b]), |acc, x| {
            Self::app(fun.clone(), vec![acc, x])
        })
    }

    #[allow(non_snake_case)]
    pub const fn True() -> Self {
        Self::constant(TRUE.const_clone())
    }

    #[allow(non_snake_case)]
    pub const fn False() -> Self {
        Self::constant(FALSE.const_clone())
    }

    pub fn and(args: implvec!(Self)) -> Self {
        let mut args = args.into_iter().filter(|x| !x.is_true()).unique();
        ereturn_let!(let Some(init) = args.next(), Self::True());
        ereturn_if!(init.is_false(), Self::False());

        let mut ret = init;
        for c in args {
            ereturn_if!(c.is_false(), Self::False());
            ret = rexp!((AND #c #ret));
        }
        ret
    }

    pub fn or(args: implvec!(Self)) -> Self {
        let mut args = args.into_iter().filter(|x| !x.is_false()).unique();
        ereturn_let!(let Some(init) = args.next(), Self::False());
        ereturn_if!(init.is_true(), Self::True());

        let mut ret = init;
        for c in args {
            ereturn_if!(c.is_true(), Self::True());
            ret = rexp!((OR #c #ret));
        }
        ret
    }

    #[deprecated]
    pub fn optimised_binder(
        _kind: FOBinder,
        _vars: implvec!(Variable),
        _arg: RecFOFormula,
    ) -> Self {
        todo!()
    }

    /// Makes a constant
    pub const fn constant(head: Function) -> Self {
        Self::App {
            head,
            args: mk_cowarc![],
        }
    }

    pub const fn mk_const_app(head: Function, args: &'static [Self]) -> Self {
        Self::App {
            head,
            args: CowArc::Borrowed(args),
        }
    }

    pub const fn mk_var(var: Variable) -> Self {
        Self::Var(var)
    }

    pub const fn mk_const_quant(
        head: FOBinder,
        vars: &'static [Variable],
        arg: &'static [Self],
    ) -> Self {
        Self::Quantifier {
            head,
            vars: CowArc::Borrowed(vars),
            arg: CowArc::Borrowed(arg),
        }
    }

    pub const fn const_clone(&self) -> Self {
        match self {
            Self::Quantifier {
                head,
                vars: CowArc::Borrowed(vars),
                arg: CowArc::Borrowed(arg),
            } => Self::Quantifier {
                head: *head,
                vars: CowArc::Borrowed(*vars),
                arg: CowArc::Borrowed(arg),
            },
            Self::App {
                head,
                args: CowArc::Borrowed(args),
            } if head.is_static() => Self::App {
                head: head.const_clone(),
                args: CowArc::Borrowed(*args),
            },
            Self::Var(variable) if variable.is_static() => Self::Var(variable.const_clone()),
            _ => panic!("not const formula"),
        }
    }
}
impl Not for RecFOFormula {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::app(NOT.clone(), vec![self])
    }
}

impl BitAnd for RecFOFormula {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::app(AND.clone(), vec![self, rhs])
    }
}

impl BitOr for RecFOFormula {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::app(OR.clone(), vec![self, rhs])
    }
}

impl Shr for RecFOFormula {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        Self::app(IMPLIES.clone(), vec![self, rhs])
    }
}