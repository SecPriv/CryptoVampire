use std::borrow::Cow;

use egg::{Analysis, EGraph, Pattern, SearchMatches, Searcher};
use static_init::dynamic;

use crate::problem::{CurrentStep, PAnalysis};
use crate::terms::{Formula, IS_INDEX, Sort};
use crate::{Lang, rexp};

pub fn mk_rewrite<N: Analysis<Lang>>() -> egg::Rewrite<Lang, N> {
    mk_rewrite!("eq_indices"; (i): (IS_INDEX #i) => (#i))
}
pub fn modify_egraph<'pbl>(egraph: &mut EGraph<Lang, PAnalysis<'pbl>>) {
    let CurrentStep { args, .. } = egraph.analysis.pbl().current_step().unwrap().clone();
    for arg in args {
        egraph.add_expr(&rexp!((IS_INDEX arg)).as_egg_ground());
    }
}

struct FindInces;

decl_vars!(pub const FOUND_INDICE:Index);

#[dynamic]
static PATTERN_SEARCH: Pattern<Lang> = <Pattern<_> as From<&Formula>>::from(&rexp!(#FOUND_INDICE));

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
            #[cfg(debug_assertions)]
            {
                print!("found index!!! {}:", egraph.id_to_expr(eclass).pretty(100));

                if egraph[eclass]
                    .leaves()
                    .any(|Lang { head, .. }| head == &IS_INDEX)
                {
                    println!("is registered")
                } else {
                    println!("is new")
                }
            }
            Some(SearchMatches {
                eclass,
                substs: vec![[(FOUND_INDICE.as_egg(), eclass)].into_iter().collect()],
                ast: Some(Cow::Borrowed(&PATTERN_SEARCH.ast)),
                // ast: None
            })
        } else {
            None
        }
    }

    fn vars(&self) -> Vec<egg::Var> {
        vec![FOUND_INDICE.as_egg()]
    }
}
