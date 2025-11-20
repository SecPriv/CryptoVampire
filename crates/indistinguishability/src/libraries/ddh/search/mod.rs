use itertools::chain;

use crate::libraries::DDH;
use crate::libraries::ddh::vars::*;
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
        // search_o_trigger,
        // search_k_trigger,
        ..
    }: &'a DDH,
) -> impl Iterator<Item = RcRule> + use<'a> {
    chain![
        prolog_rules::mk_static_rules(pbl, aenc).map(|r| r.into_mrc()),
        [dynamic::SearchRule::builder()
            .ddh(*index)
            .exec(SmtRunner::new(pbl))
            .trigger(&rexp!((search_trigger #NA #NB #TIME #PTCL #H)))
            .build()
            .into_mrc()]
    ]
}
