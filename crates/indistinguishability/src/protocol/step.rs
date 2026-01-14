use std::fmt::Display;

use bon::bon;
use egg::{Analysis, Pattern, Rewrite};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::AsFormula;

use crate::terms::{EMPTY, Formula, Function, INIT, UNFOLD_COND, UNFOLD_MSG, Variable};
use crate::{Lang, MSmt, MSmtFormula, Problem, rexp, vec_smt};

bitflags::bitflags! {
  #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
           Hash, Debug)]
  pub struct StepFlags: u8 {
      /// The function is builtin
      const PUBLICATION = 1 << 0;
  }
}

/// A step in protocol
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Step {
    /// The identifier of the step
    pub id: Function,
    /// The variables of the step
    pub vars: Vec<Variable>,
    /// The condition of the step
    pub cond: Formula,
    /// The message of the step
    pub msg: Formula,
}

impl Default for Step {
    fn default() -> Self {
        Step::builder().build().unwrap()
    }
}

#[bon]
impl Step {
    /// Creates a new step
    ///
    /// Returns `None` if the number of variables is different from the arity of the step id.
    #[builder]
    pub fn new(
        #[builder(default = INIT.clone())] id: Function,
        #[builder(with = <_>::from_iter, default = vec![])] vars: Vec<Variable>,
        #[builder(default = Formula::True())] cond: Formula,
        #[builder(default = Formula::constant(EMPTY.clone()))] msg: Formula,
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
    /// Returns the expression of the step id with its variables
    pub fn id_expr(&self) -> Formula {
        let Self { id, vars, .. } = self;
        rexp!((id #(vars.iter().map_into())*))
    }

    /// Checks if the step is valid
    ///
    /// A step is valid if all the free variables in the condition and the message
    /// are contained in the step variables.
    pub fn valid(&self) -> bool {
        let Self {
            vars, cond, msg, ..
        } = self;

        chain![cond.free_vars_iter(), msg.free_vars_iter()].all(|v| vars.contains(v))
    }
}

impl Display for Step {
    /// Formats the `Step` for display.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            id,
            vars,
            cond,
            msg,
            ..
        } = self;
        write!(
            f,
            "step {id}({}):\n\tcond: {cond}\n\tmsg: {msg}",
            vars.iter().join(", ")
        )
    }
}

impl Step {
    /// Creates an iterator of `Rewrite` rules for unfolding the condition and message of this step.
    ///
    /// These rewrites are used in the e-graph to replace `UNFOLD_COND` and `UNFOLD_MSG` applications
    /// with the actual condition and message formulas of the step.
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

    /// Creates an iterator of SMT formulas representing the unfolding of the condition and message
    /// for use with the Vampire SMT solver.
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

    pub fn mk_publish_step(id: Function, msg: Formula) -> Self {
        Self {
            id,
            vars: Vec::new(),
            cond: rexp!(true),
            msg,
        }
    }
}

#[cfg(test)]
pub mod test {}
