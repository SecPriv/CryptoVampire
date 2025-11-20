use egg::{Language, Searcher};
use golgge::{Dependancy, Rule};
use itertools::Itertools;
use utils::ereturn_let;

use super::*;
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
pub struct SubstRule;

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

        // let memo: FxHashMap<_, _> = ACCEPTABLY_EMPTY // <- recursive call where we can't substitute, whoever call this should check that ignoring those is sound
        //     .iter()
        //     .flat_map(|patt| patt.search(egraph).into_iter())
        //     .map(|s| (s.eclass, [s.eclass].into_iter().collect()))
        //     .collect(); // <- we map those to themselves

        // for subst in SUBSTITUTION_PATTERN.search(egraph) {
        //     let current_id = subst.eclass;
        //     for s in subst.substs {
        //         let [m, x, y] = [X, FROM, TO].map(|i| *s.get(i.as_egg()).unwrap());
        //         let mut memo = memo.clone();

        //         let ids = mk_substs(egraph, &mut memo, m, x, y);
        //         assert!(
        //             !ids.is_empty(),
        //             "failed substitution:\n{}",
        //             print_param(egraph, m, x, y)
        //         );
        //         for id in ids.iter() {
        //             #[cfg(debug_assertions)]
        //             if egraph.find(*id) == egraph.find(m) {
        //                 let me = egraph.id_to_expr(m);
        //                 let args = egraph[m]
        //                     .nodes
        //                     .iter()
        //                     .map(|l| {
        //                         let args = l
        //                             .children()
        //                             .iter()
        //                             .map(|id| egraph.id_to_expr(*id))
        //                             .join(" ");
        //                         format!("({} {args})", l.discriminant().name)
        //                     })
        //                     .join("\n");

        //                 panic!("should not be equal {me}:\n{args}")
        //             }

        //             egraph.union_trusted(current_id, *id, "substitution");
        //         }
        //     }
        // }

        compute_all_substitutions(egraph);

        let subst = substs
            .substs
            .into_iter()
            .map(|s| {
                // let [g, x, y] = [0, 1, 2].map(|i| *s.get(Var::from_u32(i as u32)).unwrap());
                // Substitution { egraph, x, y }.apply_subst();
                // [g]

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
}

// (msubst
// (fa_cons_m
// (lambda_find_such_that
// list_nil
// (mand
// (lt (tag idx r2_0) (r2 r2_0))
// (mand
// (eq (sel2of2 (macro_input (r2 (λS (λS r2_0))) _p$1)) (sel2of2 (macro_input (tag idx r2_0) _p$1)))
// (eq
// (sel1of2 (macro_input (λS (λS (r2 (λS (λS r2_0))))) (λS (λS _p$1))))
// (sel1of2 (macro_input (tag idx r2_0) _p$1)))))
// (mhash
// (mtuple
// (mtuple (mnonce (_nr (λS (λS r2_0)))) (sel1of2 (macro_input (r2 (λS (λS r2_0))) _p$1)))
// tag2)
// (mnonce (_mk idx λO _p$0)))
// ko)
// (fa_cons_m (macro_frame (pred (r2 r2_0)) _p$1) (fa_cons_b (macro_cond (r2 r2_0) _p$1) fa_nil)))
// (mhash
// (mtuple
// (mtuple (mnonce (_nr (λS (λS r2_0)))) (sel1of2 (macro_input (r2 (λS (λS r2_0))) _p$1)))
// tag2)
// (mnonce (_mk idx λO _p$0)))
// (mnonce n_prf))
//
//
