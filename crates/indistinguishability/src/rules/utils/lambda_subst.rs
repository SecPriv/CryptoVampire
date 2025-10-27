use egg::{Analysis, EGraph, Id};
use itertools::{Itertools, chain};
use rustc_hash::FxHashMap;

use crate::Lang;
use crate::terms::{EXISTS, FIND_SUCH_THAT, LAMBDA_O, LAMBDA_S, list};

pub fn lambda_subst<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    new_t: Id,
    current: Id,
) -> Option<Id> {
  lambda_subst_inner(egraph, &mut Default::default(), new_t, 0, current)
}

fn lambda_subst_inner<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    map: &mut FxHashMap<Id, Option<Id>>,
    new_t: Id,
    depth: usize,
    current: Id,
) -> Option<Id> {
    if let Some(&x) = map.get(&current) {
      return x;
    }
    map.insert(current, None);

    let eclass = &egraph[current].nodes.clone();
    let mut iter = eclass
        .iter()
        .filter_map(|l| lambda_subst_aux(egraph, map, new_t, depth, l));
    let fst = iter.next()?;
    for ids in iter.collect_vec() {
        egraph.union(fst, ids);
    }
    let nid = egraph.find(fst);
    map.insert(current, Some(nid));
    Some(nid)

}
fn lambda_subst_aux<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    map: &mut FxHashMap<Id, Option<Id>>,
    new_t: Id,
    depth: usize,
    Lang { head, args }: &Lang,
) -> Option<Id> {
    let mut args = args.iter();
    if head == &EXISTS || head == &FIND_SUCH_THAT {
        let sorts = *args.next().unwrap();
        let n = list::try_get_egraph(egraph, sorts).unwrap().len();
        let nids: Option<Vec<_>> = args
            .map(|&id| lambda_subst_inner(egraph, map, new_t, depth + n, id))
            .collect();
        Some(egraph.add(head.app_id(chain![[sorts], nids?])))
    } else if head == &LAMBDA_S && depth > 0 {
        lambda_subst_inner(egraph, map, new_t, depth - 1, *args.next().unwrap())
    } else if head == &LAMBDA_O && depth == 0 {
        Some(new_t)
    } else if !head.is_out_of_term_algebra() {
        let nids: Option<Vec<_>> = args
            .map(|&id| lambda_subst_inner(egraph, map, new_t, depth, id))
            .collect();
        Some(egraph.add(head.app_id(nids?)))
    } else {
        None
    }
}
