use egg::{Analysis, EGraph, Id, Language};
use itertools::Itertools;
use rustc_hash::FxHashSet;
/// Re-exports `EgraphSearcher` for e-graph based searching, `SyntaxSearcher` for syntax-based searching,
/// and `default_is_special` for determining if a function is special.
pub use subterm_trait::{EgraphSearcher, SyntaxSearcher, default_is_special};
use utils::{econtinue_if, implvec};

use crate::Lang;
use crate::problem::{PAnalysis, ProblemState};
use crate::protocol::Protocol;
use crate::terms::{Function, Sort};
/// Provides utilities for handling fresh variables and formulas.
pub mod fresh;

mod subterm_trait;

pub(crate) mod lambda_subst;

mod side;
pub use side::Side;

mod with_data;
pub use with_data::{FreshNonceSet, RuleWithFreshNonce};

/// Convenient holder for function that applies to both [Sort::Bitstring] and
/// [Sort::Bool] like subterms and candidates
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TwoSortFunction {
    /// Version of the function with sort [Sort::Bitstring]
    pub m: Function,
    /// Version of the function with sort [Sort::Bool]
    pub b: Function,
}

impl TwoSortFunction {
    pub fn form_sort(&self, s: Sort) -> Option<&Function> {
        match s {
            Sort::Bitstring => Some(&self.m),
            Sort::Bool => Some(&self.b),
            _ => None,
        }
    }

    pub fn contains(&self, other: &Function) -> bool {
        other == &self.m || other == &self.b
    }
}

pub fn find_available_id<'e>(
    egraph: &mut EGraph<Lang, PAnalysis<'e>>,
    sort: Sort,
    ids_to_check: implvec!(Id),
) -> Id {
    // *all* the subterms of `ids_to_check`
    let used_ids = all_descendants(egraph, ids_to_check, can_have_childrens);
    // the usable cached ids
    let relevant_generated_ids: FxHashSet<_> =
        ProblemState::ids_of_sort(egraph, Some(sort)).collect();
    if let Some(id) = relevant_generated_ids.difference(&used_ids).next().copied() {
        return id;
    }

    ProblemState::generate_fresh_idx(egraph, sort, "idx")
}

pub fn all_descendants<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    ancestors: implvec!(Id),
    mut can_have_childrens: impl FnMut(&Function) -> bool,
) -> FxHashSet<Id> {
    let mut todo = ancestors.into_iter().collect_vec();
    let mut descendants = FxHashSet::default();
    while let Some(x) = todo.pop() {
        econtinue_if!(descendants.contains(&x));
        descendants.insert(x);
        todo.extend(
            egraph[x]
                .nodes
                .iter()
                .filter(|f| can_have_childrens(&f.head))
                .flat_map(|f| f.children())
                .cloned(),
        );
    }
    descendants
}

fn can_have_childrens(f: &Function) -> bool {
    !f.is_alias()
}

pub fn get_protocol<'a, 'b>(
    egraph: &'b egg::EGraph<Lang, PAnalysis<'a>>,
    id: Id,
) -> Option<&'b Protocol> {
    // let id = subst.get(P.as_egg()).unwrap();
    let idx = egraph[id]
        .iter()
        .find_map(|f| f.head.get_protocol_index())?;
    // there has to be one
    egraph.analysis.pbl().protocols().get(idx)
}
