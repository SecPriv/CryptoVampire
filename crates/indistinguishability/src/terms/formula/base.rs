
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

impl RecFOFormula {
    pub fn as_var(&self) -> Option<&Variable> {
        match self {
            Self::Var(v) => Some(v),
            _ => None,
        }
    }

    /// Tries to evaluate an expression, return [None] if it can't
    pub fn try_evaluate(&self) -> Option<bool> {
        match self {
            RecFOFormula::App { head, args } => {
                match_eq! { head => {
                    TRUE => {Some(true)},
                    FALSE => {Some(false)},
                    NOT => {Some(!args[0].try_evaluate()?)},
                    AND => {
                        let l = args[0].try_evaluate();
                        let r = args[1].try_evaluate();
                        if l == Some(false) || r == Some(false) {
                            Some(false)
                        } else {
                            Some(l? && r?)
                        }
                    },
                    OR => {
                        let l = args[0].try_evaluate();
                        let r = args[1].try_evaluate();
                        if l == Some(true) || r == Some(true) {
                            Some(true)
                        } else {
                            Some(l? || r?)
                        }
                    },
                    IMPLIES => {
                        let l = args[0].try_evaluate();
                        let r = args[1].try_evaluate();
                        if l == Some(false) || r == Some(true) {
                            Some(true)
                        } else {
                            Some((!l?) || r?)
                        }
                    },
                    _ => {None}
                }}
            }
            RecFOFormula::Quantifier {
                head: FOBinder::Exists,
                arg,
                ..
            }
            | RecFOFormula::Quantifier {
                head: FOBinder::Forall,
                arg,
                ..
            } => arg[0].try_evaluate(),
            _ => None,
        }
    }


    /// Returns the [Sort] of `self`, [None] if it is a variable
    ///
    /// **NB**:
    /// - doesn't typechecks
    pub fn try_get_sort(&self) -> Option<Sort> {
        match self {
            RecFOFormula::Quantifier { .. } => Some(Sort::Bool),
            RecFOFormula::App { head, .. } => Some(head.signature.output),
            RecFOFormula::Var(_) => None,
        }
    }

    pub fn is_true(&self) -> bool {
        matches!(self, Self::App { head, .. } if head == &TRUE)
    }

    pub fn is_false(&self) -> bool {
        matches!(self, Self::App { head, .. } if head == &FALSE)
    }
}

// =========================================================
// ======================= is_xxx ==========================
// =========================================================
#[allow(dead_code)]
impl RecFOFormula {
    #[must_use]
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }
    #[must_use]
    pub fn is_app(&self) -> bool {
        matches!(self, Self::App { .. })
    }
    #[must_use]
    pub fn is_quantifier(&self) -> bool {
        matches!(self, Self::Quantifier { .. })
    }
}


fn find<'a>(
    var: &'a Variable,
    subst: &'a FxHashMap<Variable, RecFOFormula>,
    seen: &mut Vec<Variable>,
) -> Result<Either<&'a RecFOFormula, &'a Variable>, &'a Variable> {
    match subst.get(var) {
        Some(RecFOFormula::Var(nv)) if seen.contains(nv) => Err(var),
        Some(RecFOFormula::Var(var)) => {
            seen.push(var.clone());
            find(var, subst, seen)
        }
        Some(x) => Ok(Either::Left(x)),
        _ => Ok(Either::Right(var)),
    }
}


impl Default for RecFOFormula {
    fn default() -> Self {
        Self::App {
            head: TRUE.clone(),
            args: Default::default(),
        }
    }
}
impl Formula for RecFOFormula {
    type Var = Variable;

    type Fun = Function;

    type Quant = RecFOFormulaQuant;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            RecFOFormula::Quantifier { head, vars, arg } => Destructed {
                head: HeadSk::Quant(RecFOFormulaQuant::new(head, vars.as_owned())),
                args: MIter::One(arg.as_owned().into_iter()),
            },
            RecFOFormula::App { head, args } => Destructed {
                head: HeadSk::Fun(head.clone()),
                args: MIter::Many(args.as_owned().into_iter()),
            },
            RecFOFormula::Var(var) => Destructed {
                head: HeadSk::Var(var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}

impl<'b> Formula for &'b RecFOFormula {
    type Var = &'b Variable;

    type Fun = &'b Function;

    type Quant = RecFOFormulaQuantRef<'b>;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; One:A, Many:B, None:C);

        match self {
            RecFOFormula::Quantifier { head, vars, arg } => Destructed {
                head: HeadSk::Quant(RecFOFormulaQuantRef::new(*head, vars.as_ref())),
                args: MIter::One(arg.iter()),
            },
            RecFOFormula::App { head, args } => Destructed {
                head: HeadSk::Fun(head),
                args: MIter::Many(args.iter()),
            },
            RecFOFormula::Var(var) => Destructed {
                head: HeadSk::Var(var),
                args: MIter::None([].into_iter()),
            },
        }
    }
}