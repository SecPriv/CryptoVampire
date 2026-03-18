use anyhow::ensure;
use bon::{Builder, bon, builder};
use itertools::{Itertools, chain, izip};
use logic_formula::AsFormula;
use rustc_hash::{FxHashMap, FxHashSet};
use steel_derive::Steel;

use crate::rexp;
use crate::terms::{Formula, Function, INDEX_EQ, MACRO_MEMORY_CELL, MITE, PRED, Sort, Variable};
// TODO:
// - equality for indices (rewrite rule)
// - rewrite rules for state
// deal with unassigned state
// init
// - subterm
// traditionnal before a `pred`
// depency listing

#[derive(Debug, Clone, PartialEq, Eq, Hash, Steel)]
pub struct SingleAssignement {
    // #[builder(with = <_>::from_iter, default = vec![])]
    assignement_vars: Vec<Variable>,
    // #[builder(with = <_>::from_iter, default = vec![])]
    parameter_vars: Vec<Variable>,
    value: Formula,
}

pub type Assignements = FxHashMap<Function, SingleAssignement>;

#[bon]
impl SingleAssignement {
    #[builder]
    pub fn new(
        #[builder(with = <_>::from_iter, default = vec![])] assignement_vars: Vec<Variable>,
        #[builder(with = <_>::from_iter, default = vec![])] parameter_vars: Vec<Variable>,
        value: Formula,
    ) -> anyhow::Result<Self> {
        let free_vars: FxHashSet<_> = chain![&assignement_vars, &parameter_vars].collect();
        ensure!(
            (&value).free_vars_iter().all(|v| free_vars.contains(&v)),
            "free varaible"
        );
        ensure!(
            value.has_sort(Sort::Bitstring),
            "the content of a state should have sort `Bitstring`"
        );

        Ok(Self {
            assignement_vars,
            parameter_vars,
            value,
        })
    }
}

impl SingleAssignement {
    /// $c(\vec\jmath)@\tau := \textbf{if }\vec\jmath = \vec\imath \textbf{ then } m \textbf{ else } c(\vec\jmath)@\mathrm{pred}(\tau)$
    ///
    /// `c(ȷ⃗)@τ := if ȷ⃗ = ı⃗ then  m else  c(ȷ⃗)@pred(τ)`
    pub fn mk_formula(&self, fun: &Function, tau: &Formula, ptcl: &Formula) -> Formula {
        let Self {
            assignement_vars,
            parameter_vars,
            value,
        } = self;
        let js = parameter_vars.iter().cloned().map(Formula::Var);
        let is = assignement_vars.iter().cloned().map(Formula::Var);
        let id_eq = izip!(js.clone(), is).map(|(j, i)| rexp!((INDEX_EQ #j #i)));

        rexp!((MITE (and #id_eq*) #value (MACRO_MEMORY_CELL (fun #js*) (PRED #tau) #ptcl)))
    }

    pub fn assignement_vars(&self) -> &[Variable] {
        &self.assignement_vars
    }

    pub fn parameter_vars(&self) -> &[Variable] {
        &self.parameter_vars
    }
}
