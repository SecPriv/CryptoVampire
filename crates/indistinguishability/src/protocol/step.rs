use std::{fmt::Display, ops::Deref};

use cryptovampire_macros::smt;
use cryptovampire_smt::{Smt, SmtFormula, SortedVar};
use egg::{Analysis, ENodeOrVar, MultiPattern, Pattern, PatternAst, RecExpr, Rewrite, Var};
use golgge::PrologRule;
use itertools::{Itertools, chain, izip};
use log::trace;
use logic_formula::{Formula, egg::SimpleDiscriminant};

use crate::{
    Lang, LangVar, MSmt, MSmtFormula, rexp,
    terms::{Function, UNFOLD_COND, UNFOLD_MSG},
    vampire::convert::{formula_to_smt, var_to_smt},
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
    pub fn valid(&self) -> bool {
        self.cond.free_vars_iter().all(|v| self.vars.contains(&v))
            && self.msg.free_vars_iter().all(|v| self.vars.contains(&v))
    }
}

impl Display for Step {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            id,
            vars,
            cond,
            msg,
        } = self;
        write!(
            f,
            "step {id}({}):\n\tcond: {cond}\n\tmsg: {msg}",
            vars.iter().join(", ")
        )
    }
}

impl Step {
    pub(crate) fn mk_unfold_rewrites<N: Analysis<Lang>>(
        &self,
        ptcl: &Function,
    ) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
        trace!("mk unfold rw for {self}");
        let name = self.id_expr();
        let ptcl = &rexp!(ptcl).to_vec().into();

        let unfold_cond = Rewrite::new(
            format!("unfold cond {name} in {ptcl}"),
            Pattern::<Lang>::from(ProtocolLanguage::app_unfold(MacroKind::Cond, &name, ptcl)),
            Pattern::<Lang>::from(self.cond.clone()),
        )
        .unwrap();
        let unfold_msg = Rewrite::new(
            format!("unfold msg {name} in {ptcl}"),
            Pattern::<Lang>::from(ProtocolLanguage::app_unfold(MacroKind::Msg, &name, ptcl)),
            Pattern::<Lang>::from(self.msg.clone()),
        )
        .unwrap();

        [unfold_cond, unfold_msg].into_iter()
    }

    pub(crate) fn mk_unfold_vampire_rewrites(
        &self,
        ptcl: &MSmtFormula,
    ) -> impl Iterator<Item = MSmt> + use<'_> {
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

        [
            comment,
            MSmt::mk_assert(unfold_cond),
            MSmt::mk_assert(unfold_msg),
        ]
        .into_iter()
    }
}

#[cfg(test)]
pub mod test {}
