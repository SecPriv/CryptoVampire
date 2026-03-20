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
    /// The variables used in the assignement definition
    pub assignement_vars: Vec<Variable>,
    /// The variables used as parameters for the cell
    pub parameter_vars: Vec<Variable>,
    pub(crate) value: Formula,
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
        debug_assert!(
            fun.args_sorts()
                .eq(parameter_vars.iter().flat_map(Variable::get_sort))
        );
        debug_assert!(
            fun.args_sorts()
                .eq(assignement_vars.iter().flat_map(Variable::get_sort))
        );

        let js = parameter_vars.iter().cloned().map(Formula::Var);
        let is = assignement_vars.iter().cloned().map(Formula::Var);
        let id_eq = izip!(js.clone(), is).map(|(j, i)| rexp!((INDEX_EQ #j #i)));

        rexp!((MITE (and #id_eq*) #value (MACRO_MEMORY_CELL (fun #js*) (PRED #tau) #ptcl)))
    }

    pub fn mk_default_formula(
        fun: &Function,
        tau: &Formula,
        ptcl: &Formula,
    ) -> (Vec<Variable>, Formula) {
        let vars = fun.args_vars().collect_vec();
        let vars_iters = vars.iter().cloned().map(Formula::Var);
        let formula = rexp!((MACRO_MEMORY_CELL (fun #vars_iters*) (PRED #tau) #ptcl));
        (vars, formula)
    }
    
    pub fn value(&self) -> &Formula {
        &self.value
    }
}
