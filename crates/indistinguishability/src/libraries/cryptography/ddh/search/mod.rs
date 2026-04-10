use itertools::chain;

use super::vars::*;
use crate::libraries::DDH;
use crate::libraries::utils::RuleSink;
use crate::problem::{PRule, RcRule};
use crate::runners::SmtRunner;
use crate::{Problem, rexp};

mod dynamic;
mod prolog_rules;

pub fn mk_rules<'a>(
    pbl: &'a Problem,
    aenc @ DDH {
        index,
        search_trigger,
        search_trigger_mem,
        // search_o_trigger,
        // search_k_trigger,
        ..
    }: &'a DDH,
    sink: &mut impl RuleSink,
) {
    prolog_rules::mk_static_rules(pbl, aenc, sink);
    sink.add_rule(
        dynamic::SearchRule::builder()
            .ddh(*index)
            .exec(SmtRunner::new(pbl))
            .trigger(&rexp!((search_trigger #NA #NB #TIME #PTCL #H)))
            .build(),
    );
    sink.add_rule(
        dynamic::SearchRuleMem::builder()
            .ddh(*index)
            .exec(SmtRunner::new(pbl))
            .trigger_mem(&rexp!((search_trigger_mem #NA #NB #TIME #PTCL #H #C)))
            .build(),
    );
}
