use std::borrow::Cow;

use egg::{Analysis, Id, Pattern, SearchMatches, Searcher};
use static_init::dynamic;

use crate::{
    Lang, rexp,
    terms::{IS_INDEX, RecFOFormula, Sort},
};

pub fn mk_rewrite<N: Analysis<Lang>>() -> egg::Rewrite<Lang, N> {
    egg::Rewrite::new(
        "indices finder",
        FindInces,
        Pattern::from(&rexp!((IS_INDEX #FOUND_INDICE))),
    ).unwrap()
}

struct FindInces;

decl_vars!(pub const FOUND_INDICE:Index);

#[dynamic]
static PATTERN_SEARCH: Pattern<Lang> =
    <Pattern<_> as From<&RecFOFormula>>::from(&rexp!(#FOUND_INDICE));

impl<N: Analysis<Lang>> Searcher<Lang, N> for FindInces {
    fn search_eclass_with_limit(
        &self,
        egraph: &egg::EGraph<Lang, N>,
        eclass: egg::Id,
        _: usize,
    ) -> Option<SearchMatches<'_, Lang>> {
        if egraph[eclass]
            .leaves()
            .any(|Lang { head, .. }| head.signature.output == Sort::Index)
        {
            Some(SearchMatches {
                eclass,
                substs: vec![[(FOUND_INDICE.as_egg(), eclass)].into_iter().collect()],
                ast: Some(Cow::Borrowed(&PATTERN_SEARCH.ast)),
            })
        } else {
            None
        }
    }

    fn search_with_limit(
        &self,
        egraph: &egg::EGraph<Lang, N>,
        limit: usize,
    ) -> Vec<SearchMatches<'_, Lang>> {
        egraph
            .nodes()
            .iter()
            .enumerate()
            .filter(|(_, Lang { head, args })| {
                args.is_empty() && head.signature.output == Sort::Index
            })
            .take(limit)
            .map(|(i, _)| {
                let eclass = egraph.find(Id::from(i));
                SearchMatches {
                    eclass,
                    substs: vec![[(FOUND_INDICE.as_egg(), eclass)].into_iter().collect()],
                    ast: Some(Cow::Borrowed(&PATTERN_SEARCH.ast)),
                }
            })
            .collect()
    }

    fn vars(&self) -> Vec<egg::Var> {
        vec![FOUND_INDICE.as_egg()]
    }
}
