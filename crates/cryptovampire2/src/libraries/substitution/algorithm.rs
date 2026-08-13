use egg::{Analysis, EGraph, Id, Pattern, SearchMatches, Searcher};
use itertools::{Itertools, chain};
use log::{error, trace};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use static_init::dynamic;

use super::X;
use crate::libraries::substitution::{ACCEPTABLY_EMPTY, FROM, TO, is_ok_for_substitution};
use crate::terms::SUBSTITUTION;
use crate::{Lang, rexp};

#[dynamic]
static SUBSTITUTION_PATTERN: Pattern<Lang> = Pattern::from(&rexp!((SUBSTITUTION #X #FROM #TO)));

pub fn compute_all_substitutions<N: Analysis<Lang>>(egraph: &mut EGraph<Lang, N>) {
    let substs = SUBSTITUTION_PATTERN.search(egraph);

    let subst_iter = substs
        .into_iter()
        .flat_map(|SearchMatches { eclass, substs, .. }| {
            substs.into_iter().map(move |s| (eclass, s))
        });
    let mut memo = FxHashMap::default();
    let acceptably_empty = ACCEPTABLY_EMPTY // <- recursive call where we can't substitute, whoever call this should check that ignoring those is sound
        .iter()
        .flat_map(|patt| patt.search(egraph).into_iter())
        .map(|s| (s.eclass, Some(s.eclass)))
        .collect_vec();
    for (term, subst) in subst_iter {
        if egraph[term].nodes.iter().any(|l| l.head != SUBSTITUTION) {
            continue;
        }

        let x = subst.get(X.as_egg()).unwrap();
        let from = subst.get(FROM.as_egg()).unwrap();
        let to = subst.get(TO.as_egg()).unwrap();

        reset_memo(&mut memo, &acceptably_empty, from, to);
        let Some(new_x) = mk_id(egraph, &mut memo, *x) else {
            error!("{}", egraph.id_to_expr(term).pretty(100));
            continue;
        };
        trace!(
            "substitution union\nt:\n\t{}\nnew_t:\n\t{}",
            egraph.id_to_expr(term).pretty(100),
            egraph.id_to_expr(new_x).pretty(100)
        );
        egraph.union_trusted(new_x, term, "substitution");
    }
}

fn mk_id<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    memo: &mut FxHashMap<Id, Option<Id>>,
    id: Id,
) -> Option<Id> {
    if let Some(&res) = memo.get(&id) {
        return res;
    }

    memo.insert(id, None);
    let nodes = egraph[id].nodes.clone();
    let res = nodes.into_iter().find_map(|l| mk_lang(egraph, memo, l));
    memo.insert(id, res);
    res
}

fn mk_lang<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    memo: &mut FxHashMap<Id, Option<Id>>,
    Lang { head, args }: Lang,
) -> Option<Id> {
    if !is_ok_for_substitution(&head) {
        return None;
    };

    let args: Option<SmallVec<_>> = args.iter().map(|&id| mk_id(egraph, memo, id)).collect();
    Some(egraph.add_uncanonical(Lang {
        head: head.clone(),
        args: args?,
    }))
}

fn reset_memo(
    memo: &mut FxHashMap<Id, Option<Id>>,
    acceptably_empty: &[(Id, Option<Id>)],
    from: &Id,
    to: &Id,
) {
    let acceptably_empty = acceptably_empty.iter().map(|(a, b)| (*a, *b));

    memo.clear();
    memo.extend(chain![acceptably_empty, [(*from, Some(*to))]]);
}
