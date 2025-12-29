use itertools::chain;

use crate::libraries::AEnc;
use crate::libraries::aenc::vars::*;
use crate::problem::{PRule, RcRule};
use crate::runners::SmtRunner;
use crate::{Problem, rexp};

mod dynamic;
mod prolog_rules;

pub fn mk_rules<'a>(
    pbl: &'a Problem,
    aenc @ AEnc {
        index,
        search_k_trigger,
        search_o_trigger,
        ..
    }: &'a AEnc,
) -> impl Iterator<Item = RcRule> + use<'a> {
    chain![
        prolog_rules::mk_static_rules(pbl, aenc).map(|r| r.into_mrc()),
        [dynamic::SearchRule::builder()
            .aenc(*index)
            .exec(SmtRunner::new(pbl))
            .trigger_k(&rexp!((search_k_trigger #K #T #P #H)))
            .trigger_o(&rexp!((search_o_trigger #K #T #P #H)))
            .build()
            .into_mrc()]
    ]
}
