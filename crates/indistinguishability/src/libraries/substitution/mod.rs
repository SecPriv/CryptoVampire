//! definition of the `subst` rewrite rules
//!
//! ```text
//! subst(m, x, y) -> m[x -> y]
//! ```

use std::collections::hash_map::Entry;
use std::rc::Rc;

use egg::{Analysis, EGraph, Id, Language, Pattern};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use static_init::dynamic;
use utils::transposer::VecTranspose;

// use crate::rules::base_rules::substitution;
// use crate::rules::utils::mk_subst_rw;
use crate::terms::{
    Function, FunctionFlags, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, PRED, SUBSTITUTION,
    SUBSTITUTION_RULE,
};
use crate::{Lang, rexp};

declare_trace!($"substitution");

pub use rule::SubstRule;
mod rule;

mod algorithm;

mod from_proof;
pub use from_proof::{PSArgs, ProofLike, ProofSubstitution};

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
        Pattern::from(&rexp!((MACRO_INPUT #T #PTCL))),
    ]
};
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
        .filter(|l| l.head.is_ok_for_substitution())
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
                    "{} is empty: from\n\t{}\nin{}",
                    l.discriminant().name,
                    egraph.id_to_expr(m),
                    print_param(egraph, m, x, y)
                );
            }
            for arg in tranposer {
                let nid = egraph.add(l.discriminant().app_id(arg.into_iter().cloned()));
                nids.push(nid);
            }
        }
        // assert!(!nids.is_empty(), "{}", print_param(egraph, m, x, y));
    }
    let rc_ids: Rc<[_]> = nids.into_iter().unique().collect();

    // assert!(
    //     !rc_ids.is_empty(),
    //     "should not be empty\n{}",
    //     print_param(egraph, m, x, y)
    // );

    #[cfg(debug_assertions)]
    if rc_ids.len() == 1 {
        tr!("only one in subst: \n{}", print_param(egraph, m, x, y))
    }

    memo.insert(m, rc_ids.clone());
    rc_ids
}

fn is_ok_for_substitution(f: &Function) -> bool {
    f.is_ok_for_substitution()
        && (!f
            .flags
            .intersects(FunctionFlags::MACRO | FunctionFlags::UNFOLD))
}

fn print_param<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, m: Id, x: Id, y: Id) -> String {
    let [m, x, y] = [m, x, y].map(|x| egraph.id_to_expr(x).pretty(100));
    format!("in substitution m{{x|->y}}:\n\tm:\n\t{m}\n\tx:\n\t{x}\n\ty:\n\t{y}")
}
