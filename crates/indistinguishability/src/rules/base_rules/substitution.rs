//! definition of the `subst` rewrite rules
//!
//! ```text
//! subst(m, x, y) -> m[x -> y]
//! ```

use egg::{Pattern, RecExpr, Searcher, Var};
use golgge::{Dependancy, Rule};
use itertools::Itertools;
use static_init::dynamic;
use utils::ereturn_let;

use crate::{Lang, problem::PAnalysis, rexp, rules::utils::mk_subst_rw, terms::SUBSTITUTION_RULE};

#[dynamic]
static SUBSTITUTION_RULE_PATTERN: Pattern<Lang> = {
    let ast = rexp!((SUBSTITUTION_RULE #1)).to_vec();
    RecExpr::from(ast).into()
};

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
pub struct SubstRule;

impl<'a> Rule<Lang, PAnalysis<'a>> for SubstRule {
    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: egg::Id) -> Dependancy {
        let rw_rules;
        let subst = {
            let egraph = prgm.egraph_mut();
            ereturn_let!(let Some(substs) =
                SUBSTITUTION_RULE_PATTERN
                    .search_eclass(egraph, goal),
                Dependancy::impossible()
            );

            // we need to rebuild the rw rules each times because of type reasons
            rw_rules = mk_subst_rw(egraph.analysis.pbl()).collect_vec();
            substs
        };

        prgm.run_rw_rules(Some(&rw_rules));

        prgm.egraph_mut().clean = false; // <- to force a true rebuild afterward
        subst
            .substs
            .iter()
            .map(|s| [*s.get(Var::from_u32(1)).unwrap()])
            .collect()
    }
}
