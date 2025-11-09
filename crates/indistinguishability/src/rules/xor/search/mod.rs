use itertools::chain;
use crate::{
    Problem,
    problem::{PRule, RcRule},
    rexp,
    runners::SmtRunner,
};
use super::{XOr, ProofHints, vars::*};

mod dynamic;
mod prolog_rules;

pub fn mk_rules<'a>(
    pbl: &'a Problem,
    aenc @ XOr {
        index,
        search_o_trigger,
        search_k_trigger,
        ..
    }: &'a XOr,
) -> impl Iterator<Item = RcRule> + use<'a> {
    chain![
        prolog_rules::mk_static_rules(pbl, aenc).map(|r| r.into_mrc()),
        [dynamic::SearchRule::builder()
            .aenc(*index)
            .exec(SmtRunner::new(pbl))
            .trigger_k(&rexp!((search_k_trigger #K #T #P #H)))
            .trigger_o(&rexp!((search_o_trigger #K #R #T #P #H)))
            .build()
            .into_mrc()]
    ]
}
