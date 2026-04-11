use std::borrow::Cow;

use bon::Builder;
use cryptovampire_smt::{SmtFormula, SmtHead};
use itertools::Itertools;
use log::{trace, warn};
use quarck::CowArc;
use utils::{destvec, implvec};

use super::{FOBinder, Formula};
use crate::MSmtFormula;
use crate::terms::{AND, BITE, EQ, FALSE, IMPLIES, OR, TRUE};

pub trait QuantifierTranslator {
    fn try_translate(&self, f: &Formula) -> Option<Formula>;
}

#[derive(Builder)]
pub struct PreSmtRecFOFormula<'a, U> {
    formula: Cow<'a, Formula>,
    translator: &'a U,
}

/// Shortcut to keep signatures sane
pub type PreSmtRecFOFormulaF<'a, U> = PreSmtRecFOFormulaBuilder<
    'a,
    U,
    pre_smt_rec_f_o_formula_builder::SetFormula<pre_smt_rec_f_o_formula_builder::Empty>,
>;

impl<'a, U: QuantifierTranslator> TryFrom<PreSmtRecFOFormula<'a, U>> for MSmtFormula<'static> {
    type Error = Formula;

    fn try_from(
        PreSmtRecFOFormula {
            formula,
            translator,
        }: PreSmtRecFOFormula<'a, U>,
    ) -> Result<Self, Self::Error> {
        let propagate = |f: &Formula| f.as_pre_smt().translator(translator).build().try_into();
        let result = match formula.as_ref() {
            Formula::Var(variable) => Ok(Self::Var(variable.clone())),
            Formula::App { head, args } => match head.as_smt_head() {
                Some(h) => {
                    let args = args.iter().map(propagate);
                    Ok(match h {
                        SmtHead::True => Self::True,
                        SmtHead::False => Self::False,
                        SmtHead::And => Self::And(args.try_collect()?),
                        SmtHead::Or => Self::Or(args.try_collect()?),
                        SmtHead::Eq => Self::Eq(args.try_collect()?),
                        SmtHead::Neq => Self::Neq(args.try_collect()?),
                        SmtHead::Not => {
                            destvec!([a] = args; |x| {return Err(formula.into_owned())});
                            Self::Not(CowArc::new(a?))
                        }
                        SmtHead::Implies => {
                            destvec!([a, b] = args; |x| {return Err(formula.into_owned())});
                            Self::Implies(CowArc::new([a?, b?]))
                        }
                        SmtHead::If => {
                            destvec!([a, b, c] = args; |x| {return Err(formula.into_owned())});
                            Self::Ite(CowArc::new([a?, b?, c?]))
                        }
                    })
                }
                None => {
                    let args = args.iter().map(propagate).try_collect()?;
                    Ok(Self::Fun(head.clone(), args))
                }
            },
            Formula::Quantifier { head, vars, arg } => match head {
                FOBinder::Exists => {
                    Ok(Self::Exists(vars.clone(), CowArc::new(propagate(&arg[0])?)))
                }
                FOBinder::Forall => {
                    Ok(Self::Forall(vars.clone(), CowArc::new(propagate(&arg[0])?)))
                }
                FOBinder::FindSuchThat => match translator.try_translate(&formula) {
                    Some(f) => propagate(&f),
                    None => Err(formula.into_owned()),
                },
            },
        };

        #[cfg(debug_assertions)]
        if let Err(f) = &result {
            use log::error;

            error!("fail to translate to smt\n{f}")
        }
        result
    }
}

impl<'a> From<MSmtFormula<'a>> for Formula {
    fn from(value: MSmtFormula<'a>) -> Self {
        // TODO: find such that

        #[allow(unreachable_patterns)]
        match value {
            SmtFormula::Var(var) => Self::Var(var),
            SmtFormula::Fun(fun, args) => Formula::App {
                head: fun,
                args: args.into_cloned_iter().map_into().collect(),
            },
            SmtFormula::Forall(vars, formula) => {
                let arg = mk_cowarc![formula.into_inner().into()];
                Self::Quantifier {
                    head: FOBinder::Forall,
                    vars: vars.into_vec_owned(),
                    // sorts,
                    arg,
                }
            }
            SmtFormula::Exists(vars, formula) => {
                let arg = mk_cowarc![formula.into_inner().into()];
                Self::Quantifier {
                    head: FOBinder::Exists,
                    vars: vars.into_vec_owned(),
                    arg,
                }
            }
            SmtFormula::True => TRUE.rapp([]),
            SmtFormula::False => FALSE.rapp([]),
            SmtFormula::And(args) => {
                Self::fold(&AND, args.into_cloned_iter().map_into(), None, false)
            }
            SmtFormula::Or(args) => {
                Self::fold(&OR, args.into_cloned_iter().map_into(), None, false)
            }
            SmtFormula::Eq(args) => Self::fold(&EQ, args.into_cloned_iter().map_into(), None, true),
            SmtFormula::Neq(args) => {
                !Self::fold(&EQ, args.into_cloned_iter().map_into(), None, true)
            }
            SmtFormula::Not(arg) => !Self::from(arg.into_inner()),
            SmtFormula::Implies(args) => {
                let [a, b] = args.as_ref().clone().map(Self::from);
                a >> b
            }
            SmtFormula::Ite(args) => {
                Self::app(BITE.clone(), args.as_ref().clone().map(Self::from).into())
            }
            _ => unimplemented!(),
        }
    }
}

impl Formula {
    pub fn as_pre_smt<'a, U>(&'a self) -> PreSmtRecFOFormulaF<'a, U> {
        PreSmtRecFOFormula::builder().formula(Cow::Borrowed(self))
    }

    pub fn into_pre_smt<'a, U>(self) -> PreSmtRecFOFormulaF<'a, U> {
        PreSmtRecFOFormula::builder().formula(Cow::Owned(self))
    }

    pub fn as_smt<U: QuantifierTranslator>(&self, pbl: &U) -> Option<MSmtFormula<'static>> {
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

// fn collect_array<U, E, const N: usize>(iter: implvec!(Result<U, E>), err: E) -> Result<[U; N], E> {}
