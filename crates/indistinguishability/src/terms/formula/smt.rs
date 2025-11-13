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

use super::RecFOFormula;
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

pub trait QuantifierTranslator {
    fn try_translate(&self, f: &RecFOFormula) -> Option<RecFOFormula>;
}

#[derive(Builder)]
pub struct PreSmtRecFOFormula<'a, U> {
    formula: Cow<'a, RecFOFormula>,
    translator: &'a U,
}

/// Shortcut to keep signatures sane
pub type PreSmtRecFOFormulaF<'a, U> = PreSmtRecFOFormulaBuilder<
    'a,
    U,
    pre_smt_rec_f_o_formula_builder::SetFormula<pre_smt_rec_f_o_formula_builder::Empty>,
>;

impl<'a, U: QuantifierTranslator> TryFrom<PreSmtRecFOFormula<'a, U>> for MSmtFormula {
    type Error = RecFOFormula;

    fn try_from(
        PreSmtRecFOFormula {
            formula,
            translator,
        }: PreSmtRecFOFormula<'a, U>,
    ) -> Result<Self, Self::Error> {
        let propagate = |f: &RecFOFormula| f.as_pre_smt().translator(translator).build().try_into();
        let restult = match formula.as_ref() {
            RecFOFormula::Var(variable) => Ok(Self::Var(variable.clone())),
            RecFOFormula::App { head, args } => match head.as_smt_head() {
                Some(h) => {
                    let args = args.iter().map(propagate).try_collect()?;
                    Ok(match h {
                        SmtHead::True => Self::True,
                        SmtHead::False => Self::False,
                        SmtHead::And => Self::And(args),
                        SmtHead::Or => Self::Or(args),
                        SmtHead::Eq => Self::Eq(args),
                        SmtHead::Neq => Self::Neq(args),
                        SmtHead::Not => {
                            let [arg] = TryInto::<[_; _]>::try_into(args)
                                .map_err(|_| formula.into_owned())?
                                .map(Box::new);
                            Self::Not(arg)
                        }
                        SmtHead::Implies => {
                            let [a1, a2] = TryInto::<[_; _]>::try_into(args)
                                .map_err(|_| formula.into_owned())?
                                .map(Box::new);
                            Self::Implies(a1, a2)
                        }
                        SmtHead::If => {
                            let [c, l, r] = TryInto::<[_; _]>::try_into(args)
                                .map_err(|_| formula.into_owned())?
                                .map(Box::new);
                            Self::Ite(c, l, r)
                        }
                    })
                }
                None => {
                    let args = args.iter().map(propagate).try_collect()?;
                    Ok(Self::Fun(head.clone(), args))
                }
            },
            RecFOFormula::Quantifier { head, vars, arg } => match head {
                FOBinder::Exists => {
                    Ok(Self::Exists(vars.as_owned(), Box::new(propagate(&arg[0])?)))
                }
                FOBinder::Forall => {
                    Ok(Self::Forall(vars.as_owned(), Box::new(propagate(&arg[0])?)))
                }
                FOBinder::FindSuchThat => match translator.try_translate(&formula) {
                    Some(f) => propagate(&f),
                    None => Err(formula.into_owned()),
                },
            },
        };

        #[cfg(debug_assertions)]
        if let Err(f) = &restult {
            use log::error;

            error!("fail to translate to smt\n{f}")
        }
        restult
    }
}

impl From<MSmtFormula> for RecFOFormula {
    fn from(value: MSmtFormula) -> Self {
        // TODO: find such that

        #[allow(unreachable_patterns)]
        match value {
            SmtFormula::Var(var) => Self::Var(var),
            SmtFormula::Fun(fun, args) => RecFOFormula::App {
                head: fun,
                args: args.into_iter().map_into().collect(),
            },
            SmtFormula::Forall(vars, formula) => {
                let arg = mk_cowarc![Self::from(*formula)];
                Self::Quantifier {
                    head: FOBinder::Forall,
                    vars: vars.into(),
                    // sorts,
                    arg,
                }
            }
            SmtFormula::Exists(vars, formula) => {
                let arg = mk_cowarc![Self::from(*formula)];
                Self::Quantifier {
                    head: FOBinder::Exists,
                    vars: vars.into(),
                    arg,
                }
            }
            SmtFormula::True => Self::app(TRUE.clone(), vec![]),
            SmtFormula::False => Self::app(FALSE.clone(), vec![]),
            SmtFormula::And(args) => Self::fold(&AND, args.into_iter().map_into(), None, false),
            SmtFormula::Or(args) => Self::fold(&OR, args.into_iter().map_into(), None, false),
            SmtFormula::Eq(args) => Self::fold(&EQ, args.into_iter().map_into(), None, true),
            SmtFormula::Neq(args) => !Self::fold(&EQ, args.into_iter().map_into(), None, true),
            SmtFormula::Not(arg) => !Self::from(*arg),
            SmtFormula::Implies(a, b) => Self::from(*a) >> Self::from(*b),
            SmtFormula::Ite(c, l, r) => {
                Self::app(BITE.clone(), [c, l, r].map(|x| Self::from(*x)).into())
            }
            _ => unimplemented!(),
        }
    }
}

impl RecFOFormula {
    pub fn as_pre_smt<'a, U>(&'a self) -> PreSmtRecFOFormulaF<'a, U> {
        PreSmtRecFOFormula::builder().formula(Cow::Borrowed(self))
    }

    pub fn into_pre_smt<'a, U>(self) -> PreSmtRecFOFormulaF<'a, U> {
        PreSmtRecFOFormula::builder().formula(Cow::Owned(self))
    }

    pub fn as_smt<U: QuantifierTranslator>(&self, pbl: &U) -> Option<MSmtFormula> {
        trace!("trying to translate to smt:\n{self}");
        match MSmtFormula::try_from(self.as_pre_smt().translator(pbl).build()) {
            Err(f) => {
                warn!("failed to turn into smt {f}");
                None
            }
            Ok(f) => {
                trace!("translated;\n\t{self}\nto:\n\t{f}");
                Some(f)
            }
        }
    }
}
