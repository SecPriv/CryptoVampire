use egg::{
    Analysis, EGraph, ENodeOrVar, Id, Language, Pattern, SearchMatches, Searcher, Subst, Var,
};
use itertools::Itertools;
use utils::implvec;

use crate::mutils::to_owned_search_result;

use super::analysis::DependancyAnalysis;

/**
We use an [EGraph] to make out
 */
#[derive(Debug, Clone)]
pub struct Protocol<L>
where
    L: Language,
    DependancyAnalysis: Analysis<ENodeOrVar<L>>,
    <DependancyAnalysis as Analysis<ENodeOrVar<L>>>::Data: Clone,
{
    egraph: EGraph<ENodeOrVar<L>, DependancyAnalysis>,
    steps: Vec<Step>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Step {
    name: String,
    vars: Vec<Var>,
    condition: Id,
    message: Id,
}

pub fn match_one<'b, L>(
    egraph: &EGraph<L, DependancyAnalysis>,
    ptcl_egraph: &EGraph<ENodeOrVar<L>, DependancyAnalysis>,
    pattern: Id,
    term: Id,
) -> Option<SearchMatches<'b, L>>
where
    L: Language + Clone,
    DependancyAnalysis: Analysis<ENodeOrVar<L>>,
    DependancyAnalysis: Analysis<L>,
{
    Pattern::from(ptcl_egraph.id_to_expr(pattern))
        .search_eclass(egraph, term)
        .map(to_owned_search_result)
}

pub fn match_many<'a, 'b, L, I>(
    egraph: &'a EGraph<L, DependancyAnalysis>,
    ptcl_egraph: &'a EGraph<ENodeOrVar<L>, DependancyAnalysis>,
    patterns: I,
    term: Id,
) -> impl Iterator<Item = SearchMatches<'b, L>> + use<'a, 'b, L, I>
where
    L: Language + Clone + 'b,
    DependancyAnalysis: Analysis<ENodeOrVar<L>>,
    DependancyAnalysis: Analysis<L>,
    I: IntoIterator<Item = Id>,
{
    patterns
        .into_iter()
        .flat_map(move |pattern| match_one(egraph, ptcl_egraph, pattern, term))
}
