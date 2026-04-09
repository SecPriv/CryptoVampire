use itertools::chain;

use super::AEnc;
use super::vars::*;
use crate::libraries::utils::RuleSink;
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
        search_k_trigger_mem,
        search_o_trigger_mem,
        ..
    }: &'a AEnc,
    sink: &mut impl RuleSink,
) {
    prolog_rules::mk_static_rules(pbl, aenc, sink);
    sink.add_rule(
        dynamic::SearchRule::builder()
            .aenc(*index)
            .exec(SmtRunner::new(pbl))
            .trigger_k(&rexp!((search_k_trigger #K #T #P #H)))
            .trigger_o(&rexp!((search_o_trigger #K #T #P #H)))
            .build(),
    );
    sink.add_rule(
        dynamic::SearchRuleMem::builder()
            .aenc(*index)
            .exec(SmtRunner::new(pbl))
            .trigger_k_mem(&rexp!((search_k_trigger_mem #K #T #P #H #C)))
            .trigger_o_mem(&rexp!((search_o_trigger_mem #K #T #P #H #C)))
            .build(),
    );
}
