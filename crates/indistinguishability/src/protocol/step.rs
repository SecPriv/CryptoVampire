use std::{fmt::Display, ops::Deref};

use cryptovampire_macros::smt;
use cryptovampire_smt::{Smt, SmtFormula, SortedVar};
use egg::{Analysis, ENodeOrVar, MultiPattern, Pattern, PatternAst, RecExpr, Rewrite, Var};
use golgge::PrologRule;
use itertools::{chain, izip, Itertools};
use logic_formula::egg::SimpleDiscriminant;

use crate::{
    rules::vampire::{convert::formula_to_smt, convert::var_to_smt, MSmt, MSmtFormula},
    terms::{Function, UNFOLD_COND, UNFOLD_MSG},
    Lang, LangVar,
};

use super::{MacroKind, ProtocolLanguage};

/// A step in protocol
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Step {
    pub id: Function,
    pub vars: Vec<Var>,
    pub cond: PatternAst<Lang>,
    pub msg: PatternAst<Lang>,
}

impl Step {
    pub(crate) fn max_vars(&self) -> u32 {
        self.vars
            .iter()
            .filter_map(Var::as_u32)
            .max()
            .unwrap_or_default()
    }

    pub fn id_expr(&self) -> RecExpr<LangVar> {
        self.id.app_var(
            &self
                .vars
                .iter()
                .map(|x| [ENodeOrVar::Var(*x)])
                .collect::<Vec<_>>(),
        )
    }
}

impl Step {
    pub(crate) fn mk_unfold_rewrites<N: Analysis<Lang>>(
        &self,
        ptcl: &PatternAst<Lang>,
    ) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
        let name = self.id_expr();

        let unfold_cond = Rewrite::new(
            format!("unfold cond {name}"),
            Pattern::<Lang>::from(ProtocolLanguage::app_unfold(MacroKind::Cond, &name, ptcl)),
            Pattern::<Lang>::from(self.cond.clone()),
        )
        .unwrap();
        let unfold_msg = Rewrite::new(
            format!("unfold msg {name}"),
            Pattern::<Lang>::from(ProtocolLanguage::app_unfold(MacroKind::Msg, &name, ptcl)),
            Pattern::<Lang>::from(self.msg.clone()),
        )
        .unwrap();

        [unfold_cond, unfold_msg].into_iter()
    }

    pub(crate) fn mk_unfold_vampire_rewrites(
        self,
        ptcl: &MSmtFormula,
    ) -> impl Iterator<Item = MSmt> {
        use Smt::*;
        let [cond, msg, name] =
            [self.cond.as_ref(), &self.msg, &self.id_expr()].map(formula_to_smt);

        let sorted_vars: Vec<_> = izip!(self.id.signature.inputs.iter(), self.vars.iter())
            .map(|(a, b)| (*a, var_to_smt(b)))
            .map(|(sort, var)| SortedVar { var, sort })
            .collect();

        let comment = Comment(format!("unfolding of {name}"));
        let unfold_cond = smt! {
            (forall #(sorted_vars.clone()) (= (UNFOLD_COND #name #ptcl) #cond))
        };
        let unfold_msg = smt! {
            (forall #(sorted_vars.clone()) (= (UNFOLD_MSG #name #ptcl) #msg))
        };

        [comment, Assert(unfold_cond), Assert(unfold_msg)].into_iter()
    }
}
