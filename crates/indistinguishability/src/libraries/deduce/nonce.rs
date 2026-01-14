use std::borrow::Cow;

use egg::{Pattern, Searcher};
use golgge::{Dependancy, Program, Rule};
use itertools::Itertools;
use static_init::dynamic;

use crate::problem::PAnalysis;
use crate::terms::{BIT_DEDUCE, FRESH_NONCE, NONCE};
use crate::{Lang, rexp};

#[derive(Debug, Clone, Copy)]
pub struct DeduceNonceRule;

decl_vars!(const U, V, X, H1, H2);

#[dynamic]
static DEDUCE_NONCE_PATTERN: Pattern<Lang> =
    Pattern::from(&rexp!((BIT_DEDUCE #U #V (NONCE #X) (NONCE #X) #H1 #H2)));

#[dynamic]
static DEDUCE_NONCE_SUBGOALS: [Pattern<Lang>; 2] = [
    Pattern::from(&rexp!((FRESH_NONCE #X #U #H1))),
    Pattern::from(&rexp!((FRESH_NONCE #X #V #H2))),
];

impl<'a, R> Rule<Lang, PAnalysis<'a>, R> for DeduceNonceRule {
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("deduce fresh nonces (custom)")
    }

    fn search(&self, prgm: &mut Program<Lang, PAnalysis<'a>, R>, goal: egg::Id) -> Dependancy {
        let matches = DEDUCE_NONCE_PATTERN.search_eclass(prgm.egraph(), goal);
        let mut ret = Vec::new();

        if let Some(subst) = matches {
            for subst in &subst.substs {
                let x = subst[X.as_egg()];

                let nonce_func = prgm.egraph()[x]
                    .nodes
                    .iter()
                    .find(|Lang { head, .. }| head.is_nonce() && !head.is_fresh())
                    .map(|n| n.head.clone());

                if let Some(f) = nonce_func {
                    prgm.egraph_mut()
                        .analysis
                        .pbl_mut()
                        .register_potential_public_nonce(f);
                }

                ret.push(
                    DEDUCE_NONCE_SUBGOALS
                        .iter()
                        .map(|g| g.apply_susbt(prgm.egraph_mut(), subst))
                        .collect_vec(),
                );
            }
        }

        ret.into_iter().collect()
    }

    fn debug(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "deduce-fresh-nonce")
    }
}
