use std::cell::RefCell;

use anyhow::{Context, ensure};
use itertools::{Itertools, chain};
use logic_formula::iterators::AllTermsIterator;
use logic_formula::outers::{RefCellPile, RefPile};
use logic_formula::{AsFormula, IteratorHelper};
use rustc_hash::FxHashSet;
use utils::powerset::{PowersetReverse, PowersetReverseIter};

use crate::Problem;
use crate::protocol::Step;
use crate::terms::{Formula, Function, FunctionFlags, Sort, Variable};

pub type MI = impl Iterator<Item = Vec<Function>>;

pub enum NoncePublicSearchState {
    /// the solver is gathering likely candidates
    Gather(FxHashSet<Function>),
    /// The server doing the guided bruteforcing the search
    Run(MI),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PublicTerm {
    pub vars: Vec<Variable>,
    pub term: Formula,
}

impl PublicTerm {
    pub fn is_valid(&self) -> bool {
        (&self.term).free_vars_iter().all(|v| self.vars.contains(v))
    }
}

impl Problem {
    pub fn publish(&mut self, term: PublicTerm) -> anyhow::Result<Function> {
        ensure!(
            term.term.try_get_sort() == Some(Sort::Bitstring),
            "the published term must have sort Bitstring got {:?} for\n{}",
            term.term.try_get_sort(),
            term.term
        );
        ensure!(
            term.is_valid(),
            "All variables in a published terms should be bound"
        );

        self.cache.smt.force_reset();

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

        Ok(step)
    }

    pub fn register_potential_public_nonce(&mut self, nonce: Function) {
        use NoncePublicSearchState::*;
        if let Gather(x) = &mut self.nonce_finder {
            x.insert(nonce);
        }
    }

    /// Switch from information gathering to bruteforcing
    ///
    /// Returns `true` to the switch did indeed happen
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

/// Generates a non-stupid order of set nonce to try to publish.
#[define_opaque(MI)]
fn mk_iterator(candidates: FxHashSet<Function>, pbl: &Problem) -> MI {
    let already_used: FxHashSet<_> = mk_blocked_by_published_iter(pbl);

    let filter = move |n: &Function| !(n.is_fresh() || already_used.contains(n));

    let to_test_first = candidates.into_iter().filter(&filter).collect_vec();
    let others = pbl
        .functions()
        .nonces()
        .filter(|&x| filter(x))
        .cloned()
        .collect_vec();

    let to_test_first = PowersetReverse::new(to_test_first);
    let others = PowersetReverse::new(others);
    chain!(to_test_first, others)
        .filter(|x| !x.is_empty())
        .unique()
}

fn mk_blocked_by_published_iter<I: FromIterator<Function>>(pbl: &Problem) -> I {
    let pile = RefCell::new(Vec::new());

    pbl.protocols()
        .iter()
        .flat_map(|p| p.steps().iter())
        .filter(|s| s.id.is_publish_step())
        .map(|s| &s.msg)
        .flat_map(|f| {
            let mut iter = RefCellPile::new(&pile, AllTermsIterator);
            iter.as_mut().push_child(f, ());
            iter
        })
        .filter_map(|f| {
            if let Formula::App { head, .. } = f
                && head.signature.output == Sort::Nonce
            {
                Some(head)
            } else {
                None
            }
        })
        .cloned()
        .collect()
}
