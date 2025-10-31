//! definition of the `subst` rewrite rules
//!
//! ```text
//! subst(m, x, y) -> m[x -> y]
//! ```

use std::collections::hash_map::Entry;
use std::rc::Rc;

use egg::{Analysis, EGraph, Id, Language, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use static_init::dynamic;
use utils::ereturn_let;
use utils::transposer::VecTranspose;

use crate::problem::PAnalysis;
// use crate::rules::base_rules::substitution;
// use crate::rules::utils::mk_subst_rw;
use crate::terms::{MACRO_EXEC, MACRO_FRAME, PRED, SUBSTITUTION, SUBSTITUTION_RULE};
use crate::{Lang, rexp};

declare_trace!($"substitution");

decl_vars!(const; GOAL:Bool, X:Any, FROM:Bitstring, TO:Bitstring, PTCL:Protocol, T:Time);

#[dynamic]
static SUBSTITUTION_RULE_PATTERN: Pattern<Lang> = Pattern::from(&rexp!((SUBSTITUTION_RULE #GOAL)));

#[dynamic]
static SUBSTITUTION_PATTERN: Pattern<Lang> = Pattern::from(&rexp!((SUBSTITUTION #X #FROM #TO)));

#[dynamic]
static ACCEPTABLY_EMPTY: Vec<Pattern<Lang>> = {
    vec![
        Pattern::from(&rexp!((MACRO_EXEC (PRED #T) #PTCL))),
        Pattern::from(&rexp!((MACRO_FRAME (PRED #T) #PTCL))),
    ]
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
    /// Searches for `SUBSTITUTION_RULE` patterns in the e-graph and applies substitutions.
    ///
    /// This rule identifies goals that need substitution, performs the substitution
    /// using `mk_substs`, and then rebuilds the e-graph with the new terms.
    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: egg::Id) -> Dependancy {
        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs) =
            SUBSTITUTION_RULE_PATTERN
                .search_eclass(egraph, goal),
            Dependancy::impossible()
        );
        tr!("substitution");

        let memo: FxHashMap<_, _> = ACCEPTABLY_EMPTY // <- recursive call where we can't substitute, whoever call this should check that ignoring those is sound
            .iter()
            .flat_map(|patt| patt.search(egraph).into_iter())
            .map(|s| (s.eclass, [s.eclass].into_iter().collect()))
            .collect(); // <- we map those to themselves

        for subst in SUBSTITUTION_PATTERN.search(egraph) {
            let current_id = subst.eclass;
            for s in subst.substs {
                let [m, x, y] = [X, FROM, TO].map(|i| *s.get(i.as_egg()).unwrap());
                let mut memo = memo.clone();

                let ids = mk_substs(egraph, &mut memo, m, x, y);
                assert!(!ids.is_empty());
                for id in ids.iter() {
                    #[cfg(debug_assertions)]
                    if egraph.find(*id) == egraph.find(m) {
                        let me = egraph.id_to_expr(m);
                        let args = egraph[m]
                            .nodes
                            .iter()
                            .map(|l| {
                                let args = l
                                    .children()
                                    .iter()
                                    .map(|id| egraph.id_to_expr(*id))
                                    .join(" ");
                                format!("({} {args})", l.discriminant().name)
                            })
                            .join("\n");

                        panic!("should not be equal {me}:\n{args}")
                    }

                    egraph.union_trusted(current_id, *id, "substitution");
                }
            }
        }

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
            .collect();

        egraph.clean = false; // <- to force a true rebuild afterward
        subst
    }
}

/// computes `m{x |-> y}`
///
/// with `memo` for memoisation
///
/// This function recursively applies the substitution `x |-> y` to the e-graph node `m`,
/// using memoization to avoid redundant computations.
fn mk_substs<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    memo: &mut FxHashMap<Id, Rc<[Id]>>,
    m: Id,
    x: Id,
    y: Id,
) -> Rc<[Id]> {
    let m = egraph.find(m);
    let x = egraph.find(x);
    if m == x {
        return Rc::new([y]);
    }
    match memo.entry(m) {
        Entry::Occupied(occupied_entry) => return occupied_entry.get().clone(),
        Entry::Vacant(vacant_entry) => {
            vacant_entry.insert(Default::default());
        }
    }

    let eclass = &egraph[m];
    let mut nids: Vec<_> = Default::default();

    let fileterd_heads = eclass
        .nodes
        .iter()
        .filter(|l| !l.discriminant().is_special_subterm() || l.discriminant().is_if_then_else())
        .cloned()
        .collect_vec();

    if fileterd_heads.is_empty() {
        tr!("head is empty: {}", egraph.id_to_expr(m));
        nids = vec![m];
    }

    for l in fileterd_heads {
        let n_children = l
            .children()
            .iter()
            .map(|id| mk_substs(egraph, memo, *id, x, y))
            .collect_vec();

        if n_children.is_empty() {
            nids.push(m);
        } else {
            let tranposer = VecTranspose::new(&n_children);
            if tranposer.is_empty() {
                tr!(
                    "{} is empty (from {})",
                    l.discriminant().name,
                    egraph.id_to_expr(m)
                );
            }
            for arg in tranposer {
                let nid = egraph.add(l.discriminant().app_id(arg.into_iter().cloned()));
                nids.push(nid);
            }
        }
        assert!(!nids.is_empty());
    }
    let rc_ids: Rc<[_]> = nids.into_iter().unique().collect();

    assert!(
        !rc_ids.is_empty(),
        "should not be empty {}{{{} -> {}}}",
        egraph.id_to_expr(m),
        egraph.id_to_expr(x),
        egraph.id_to_expr(y)
    );

    #[cfg(debug_assertions)]
    if rc_ids.len() == 1 {
        tr!(
            "only one in subst: \nm = ({m}) {}\nx = ({x}) {}\ny = ({y}) {}",
            egraph.id_to_expr(m),
            egraph.id_to_expr(x),
            egraph.id_to_expr(y)
        )
    }

    memo.insert(m, rc_ids.clone());
    rc_ids
}
