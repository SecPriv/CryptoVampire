use std::borrow::Cow;

use egg::{Language, Searcher};
use golgge::{Dependancy, Rule};
use itertools::Itertools;
use utils::ereturn_let;

use super::*;
use crate::libraries::Library;
use crate::libraries::substitution::algorithm::compute_all_substitutions;
use crate::problem::PAnalysis;
// use crate::rules::base_rules::substitution;
// use crate::rules::utils::mk_subst_rw;
use crate::terms::SUBSTITUTION;
use crate::{CVProgram, Lang};

/// This rule is a no op logic wise.
///
/// It boxes a goal that will release to [`golgge`] after rebuilding the egraph
/// with the substitution rules.
/// ```text
///      goal
/// -------------
///  subst(goal)
/// ```
#[derive(Clone)]
struct SubstRule;

impl<'a, R> Rule<Lang, PAnalysis<'a>, R> for SubstRule {
    /// Searches for `SUBSTITUTION_RULE` patterns in the e-graph and applies substitutions.
    ///
    /// This rule identifies goals that need substitution, performs the substitution
    /// using `mk_substs`, and then rebuilds the e-graph with the new terms.
    fn search(&self, prgm: &mut CVProgram<'a, R>, goal: egg::Id) -> Dependancy {
        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs) =
            SUBSTITUTION_RULE_PATTERN
                .search_eclass(egraph, goal),
            Dependancy::impossible()
        );
        tr!("substitution");

        compute_all_substitutions(egraph);

        let subst = substs
            .substs
            .into_iter()
            .map(|s| {
                let g = *s.get(GOAL.as_egg()).unwrap();
                [g]
            })
            .take(1)
            .collect();

        #[cfg(debug_assertions)]
        {
            egraph.rebuild();
            for s in SUBSTITUTION_PATTERN.search(egraph) {
                if egraph[s.eclass]
                    .nodes
                    .iter()
                    .all(|f| f.head == SUBSTITUTION)
                {
                    panic!(
                        "substitution failed, please inspect\n{}\n{s:?}",
                        egraph.id_to_expr(s.eclass).pretty(100)
                    )
                }
            }
        }

        egraph.clean = false; // <- to force a true rebuild afterward
        subst
    }

    fn name(&self) -> std::borrow::Cow<'_, str> {
        Cow::Borrowed("default subtitution")
    }
}

pub struct SubstLib;

impl Library for SubstLib {
    fn add_rules(&self, _: &mut crate::Problem, sink: &mut impl crate::libraries::utils::RuleSink) {
        sink.add_rule(SubstRule);
    }
}
