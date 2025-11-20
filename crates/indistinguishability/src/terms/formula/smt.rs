use std::borrow::Cow;

use bon::Builder;
use cryptovampire_smt::{SmtFormula, SmtHead};
use itertools::Itertools;
use log::{trace, warn};

use super::{FOBinder, Formula};
use crate::MSmtFormula;
use crate::terms::{AND, BITE, EQ, FALSE, OR, TRUE};

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

impl<'a, U: QuantifierTranslator> TryFrom<PreSmtRecFOFormula<'a, U>> for MSmtFormula {
    type Error = Formula;

    fn try_from(
        PreSmtRecFOFormula {
            formula,
            translator,
        }: PreSmtRecFOFormula<'a, U>,
    ) -> Result<Self, Self::Error> {
        let propagate = |f: &Formula| f.as_pre_smt().translator(translator).build().try_into();
        let restult = match formula.as_ref() {
            Formula::Var(variable) => Ok(Self::Var(variable.clone())),
            Formula::App { head, args } => match head.as_smt_head() {
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
            Formula::Quantifier { head, vars, arg } => match head {
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

impl From<MSmtFormula> for Formula {
    fn from(value: MSmtFormula) -> Self {
        // TODO: find such that

        #[allow(unreachable_patterns)]
        match value {
            SmtFormula::Var(var) => Self::Var(var),
            SmtFormula::Fun(fun, args) => Formula::App {
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

impl Formula {
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
