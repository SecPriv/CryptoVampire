use anyhow::{Context, ensure};
use itertools::{Itertools, chain};
use rustc_hash::FxHashSet;

use crate::protocol::Step;
use crate::terms::{Formula, Function, FunctionFlags, LT, Sort, Variable};
use crate::{Problem, decl_vars, fresh, rexp};

pub type MI = impl Iterator<Item = Vec<Function>>;

pub enum NoncePublicSearchState {
    Gather(FxHashSet<Function>),
    Run(MI),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PublicTerm {
    pub vars: Vec<Variable>,
    pub term: Formula,
}

impl Problem {
    pub fn publish(&mut self, term: PublicTerm) -> anyhow::Result<Function> {
        ensure!(
            term.term.try_get_sort() == Some(Sort::Bitstring),
            "the published term must have sort Bitstring"
        );

        self.clear_smt_prelude();

        self.public_terms.push(term.clone());
        let n = self.num_steps()?.into();
        let sorts: Option<Vec<_>> = term.vars.iter().map(|v| v.get_sort()).collect();
        let sorts = sorts.with_context(|| "one variable doesn't have a sort")?;
        let step = self
            .declare_function()
            .inputs(sorts)
            .step(n)
            .fresh_name("publish")
            .flag(FunctionFlags::PUBLICATION_STEP)
            .call();

        let PublicTerm { vars, term } = term;
        let nptcl = self.num_protocols();
        let vars = vars.iter().cloned();
        self.push_steps((0..nptcl).map(|_| {
            Step::builder()
                .id(step.clone())
                .vars(vars.clone())
                .msg(term.clone())
                .build()
                .unwrap()
        }));

        // {
        //     // publication steps are the smallest steps

        //     let vars = vars
        //         .map(|v| v.freshen().as_formula())
        //         .collect_vec()
        //         .into_iter();
        //     let non_publish_steps = self
        //         .steps()
        //         .with_context(|| "no protocols")?
        //         .filter(|s| !s.is_publish_step())
        //         .collect_vec();

        //     for s in non_publish_steps {
        //         let other_vars = s.args_sorts().map(|x| fresh!(x).as_formula());
        //         self.add_constrain(&rexp!((LT (step #(vars.clone())*) (s #other_vars*))))?;
        //     }
        // }

        Ok(step)
    }

    pub fn register_potential_public_nonce(&mut self, nonce: Function) {
        use NoncePublicSearchState::*;
        if let Gather(x) = &mut self.nonce_finder {
            x.insert(nonce);
        }
    }

    pub fn switch_to_run_public_nonce(&mut self) -> bool {
        use NoncePublicSearchState::*;
        match &mut self.nonce_finder {
            Run(_) => false,
            Gather(x) => {
                let candidates = ::std::mem::take(x);
                let iter: MI = mk_iterator(candidates, self);
                let new_state = Run(iter);
                self.nonce_finder = new_state;
                true
            }
        }
    }
}

impl NoncePublicSearchState {}

impl Default for NoncePublicSearchState {
    fn default() -> Self {
        Self::Gather(Default::default())
    }
}

#[define_opaque(MI)]
fn mk_iterator(candidates: FxHashSet<Function>, pbl: &Problem) -> MI {
    let to_test_first = candidates
        .into_iter()
        .powerset()
        .collect_vec()
        .into_iter()
        .rev();
    let others = pbl
        .functions()
        .nonces()
        .cloned()
        .collect_vec()
        .into_iter()
        .powerset();
    chain!(to_test_first, others).unique()
}
