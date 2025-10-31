use std::fmt::Display;

use bon::bon;
use egg::{Analysis, Pattern, Rewrite};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::Formula;


use crate::terms::{EMPTY, Function, INIT, RecFOFormula, UNFOLD_COND, UNFOLD_MSG, Variable};
use crate::{Lang, MSmt, MSmtFormula, Problem, rexp, vec_smt};

/// A step in protocol
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Step {
    pub id: Function,
    pub vars: Vec<Variable>,
    pub cond: RecFOFormula,
    pub msg: RecFOFormula,
}

#[bon]
impl Step {
    #[builder]
    pub fn new(
        #[builder(default = INIT.clone())] id: Function,
        #[builder(with = <_>::from_iter, default = vec![])] vars: Vec<Variable>,
        #[builder(default = RecFOFormula::True())] cond: RecFOFormula,
        #[builder(default = RecFOFormula::constant(EMPTY.clone()))] msg: RecFOFormula,
    ) -> Option<Step> {
        (vars.len() == id.signature.arity()).then_some(Self {
            id,
            vars,
            cond,
            msg,
        })
    }
}

impl Step {
    pub fn id_expr(&self) -> RecFOFormula {
        let Self { id, vars, .. } = self;
        rexp!((id #(vars.iter().map_into())*))
    }

    pub fn valid(&self) -> bool {
        let Self {
            vars, cond, msg, ..
        } = self;

        chain![cond.free_vars_iter(), msg.free_vars_iter()].all(|v| vars.contains(v))
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
        let name = &self.id_expr();
        let ptcl = &rexp!(ptcl);

        let unfold_cond = Rewrite::new(
            format!("unfold cond {name} in {ptcl}"),
            Pattern::from(&rexp!((UNFOLD_COND #name #ptcl))),
            Pattern::from(&self.cond),
        )
        .unwrap();
        let unfold_msg = Rewrite::new(
            format!("unfold msg {name} in {ptcl}"),
            Pattern::from(&rexp!((UNFOLD_MSG #name #ptcl))),
            Pattern::from(&self.msg),
        )
        .unwrap();

        [unfold_cond, unfold_msg].into_iter()
    }

    pub(crate) fn mk_unfold_vampire_rewrites(
        &self,
        pbl: &Problem,
        ptcl: &MSmtFormula,
    ) -> impl Iterator<Item = MSmt> + use<'_> {
        let [cond, msg, name]: [MSmtFormula; _] =
            [&self.cond, &self.msg, &self.id_expr()].map(|x| x.as_smt(pbl).unwrap());
        let vars = self.vars.iter().cloned();

        vec_smt![%
            ; format!("unfolding of {name}"),
            (forall !(vars.clone()) (= (UNFOLD_COND #name #ptcl) #cond)),
            (forall !(vars.clone()) (= (UNFOLD_MSG #name #ptcl) #msg))
        ]
        .into_iter()
    }
}

#[cfg(test)]
pub mod test {}
