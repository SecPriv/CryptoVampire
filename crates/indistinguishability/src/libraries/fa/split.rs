use egg::{Analysis, EGraph, Id, Pattern, Searcher, Subst};
use itertools::{Itertools, izip};
use smallvec::{SmallVec, smallvec};
use static_init::dynamic;

use crate::libraries::fa::*;
use crate::terms::{
    CONS_FA_BITSTRING, CONS_FA_BOOL, EMPTY, FROM_BOOL, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MITE,
    NIL_FA, PRED, Sort, TUPLE,
};
use crate::{Lang, rexp};

#[dynamic]
static PATTERN_LIST_M: Pattern<Lang> = Pattern::from(&rexp!((CONS_FA_BITSTRING #HD #TL)));
#[dynamic]
static PATTERN_LIST_B: Pattern<Lang> = Pattern::from(&rexp!((CONS_FA_BOOL #HD #TL)));
#[dynamic]
static PATTERN_LIST_TUPLE: Pattern<Lang> = Pattern::from(&rexp!((TUPLE #HD #TL)));

#[dynamic]
static PATTERN_SKIP_BOILER_PLATE: Pattern<Lang> = Pattern::from(&rexp!((TUPLE
  (TUPLE (FROM_BOOL (MACRO_EXEC #T #P)) (MITE (MACRO_EXEC #T #P) #M EMPTY))
  (MACRO_FRAME (PRED #T) #P)
)));

#[dynamic]
static PATTERN_NIL: Pattern<Lang> = Pattern::from(&rexp!(NIL_FA));

/// Main splitting function. It splits `fa` once
///
/// Since we are now taking equality into account, it returns a list of the
/// splitted `fa`.
///
/// Few notable things:
/// - in practice, it shouldn't go beyond 3 elemts. We're using a [SmallVec]
///   here because all should be small
/// - the [PATTERN_SKIP_BOILER_PLATE] path quits immediatly
/// - constants gets dropped (according to [is_constant]) this notably means
///   that the returned list **can be empty**.
pub fn split<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    fa @ FaElem { a: ida, b: idb, .. }: FaElem,
) -> Vec<SmallVec<[FaElem; 3]>> {
    assert!(fa.splittable);
    fa.checks_sort(egraph);

    tr!("spliting {}", fa.display(egraph));

    if let Some(ma) = PATTERN_SKIP_BOILER_PLATE.search_eclass(egraph, ida)
        && let Some(mb) = PATTERN_SKIP_BOILER_PLATE.search_eclass(egraph, idb)
    {
        let iter = ma
            .substs
            .iter()
            .cartesian_product(mb.substs.iter())
            .map(|(sa, sb)| {
                let ntodos_a = extra_shortcut_pattern(egraph, sa);
                let ntodos_b = extra_shortcut_pattern(egraph, sb);
                izip!(ntodos_a, ntodos_b)
                    .map(|((ida, sorta), (idb, sortb))| {
                        debug_assert_eq!(sorta, sortb);
                        FaElem {
                            a: ida,
                            b: idb,
                            sort: sorta,
                            splittable: true,
                        }
                    })
                    .collect()
            });
        return iter.collect();
    }

    if is_constant(egraph, ida) && is_constant(egraph, idb) {
        tr!("drop constant:\n\t{}", fa.display(egraph));
        // return Some(res);
        return Vec::new();
    }

    let mut res = Vec::new();

    let iter = egraph[ida]
        .nodes
        .iter()
        .cartesian_product(egraph[idb].nodes.iter());

    let n = res.len();
    // for Lang { head, args } in &egraph[id].nodes {
    for (
        Lang { head, args: argsa },
        Lang {
            head: hb,
            args: argsb,
        },
    ) in iter
    {
        if (head.is_prolog_only() || hb.is_prolog_only()) && !head.is_quantifier() {
            // we skip, there *will* be another one
            continue;
        } else if head == hb && (head == &TUPLE || head == &CONS_FA_BITSTRING) {
            res.push(smallvec![
                FaElem {
                    a: argsa[0],
                    b: argsb[0],
                    sort: LSort::Bitstring,
                    splittable: true
                },
                FaElem {
                    a: argsa[1],
                    b: argsb[1],
                    sort: LSort::Bitstring,
                    splittable: true
                },
            ])
        } else if head == hb && (head == &CONS_FA_BOOL) {
            res.push(smallvec![
                FaElem {
                    a: argsa[0],
                    b: argsb[0],
                    sort: LSort::Bool,
                    splittable: true
                },
                FaElem {
                    a: argsa[1],
                    b: argsb[1],
                    sort: LSort::Bitstring,
                    splittable: true
                },
            ]);
        } else {
            res.push(smallvec![FaElem {
                splittable: false,
                ..fa
            }]);
        };
    }
    assert!(
        res.len() > n,
        "needs to go through a non prolog-only branch"
    );
    res
}

fn extra_shortcut_pattern<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    subts: &Subst,
) -> [(Id, LSort); 3] {
    let t = *subts.get(T.as_egg()).unwrap();
    let p = *subts.get(P.as_egg()).unwrap();
    let pred_t = egraph.lookup(PRED.app_id([t])).unwrap();
    let mframe = egraph.lookup(MACRO_FRAME.app_id([pred_t, p])).unwrap();
    let mmsg = *subts.get(M.as_egg()).unwrap();
    // egraph.lookup(MACRO_MSG.app_id([t, p])).unwrap();
    let mcond = egraph.lookup(MACRO_COND.app_id([t, p])).unwrap();
    [
        (mframe, LSort::Bitstring),
        (mmsg, LSort::Bitstring),
        (mcond, LSort::Bool),
    ]
}

pub fn is_constant<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> bool {
    egraph[id]
        .nodes
        .iter()
        .filter(|f| f.head.is_part_of_F())
        .any(|Lang { head, .. }| head.args_sorts().all(|s| !s.is_base() && s != Sort::Nonce))
}
