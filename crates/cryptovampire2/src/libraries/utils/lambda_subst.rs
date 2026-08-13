use std::cell::RefCell;

use egg::{Analysis, EGraph, Id};
use itertools::chain;
use log::trace;
use rustc_hash::FxHashMap;
use utils::ereturn_if;

use crate::Lang;
use crate::terms::{EXISTS, FIND_SUCH_THAT, Function, LAMBDA_O, LAMBDA_S, list};

// pub fn lambda_subst<N: Analysis<Lang>>(
//     egraph: &mut EGraph<Lang, N>,
//     new_t: Id,
//     current: Id,
//     depth: usize,
// ) -> Option<Id> {
//   lambda_subst_inner(egraph, &mut Default::default(), new_t, 0, current)
// }

/// Performs lambda substitution on an e-graph.
///
/// This function substitutes `LAMBDA_O` with `new_t` at a specific `depth` within the e-graph node `current`.
/// It uses memoization (`map`) to optimize recursive calls.
pub fn lambda_subst<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    map: &mut FxHashMap<Id, Option<Id>>,
    // the new term
    new_t: Id,
    // how 'far' is the variables we aim for
    depth: usize,
    current: Id,
) -> Option<Id> {
    if let Some(&x) = map.get(&current) {
        trace!(
            "lambda: cached:\n\tfrom:{},\n\tto:{:?}",
            egraph.id_to_expr(current).pretty(100),
            x.map(|x| egraph.id_to_expr(x).pretty(100))
        );
        return x;
    }

    // If you are a variable, shortcut
    if let Some(n) = get_variable_n(current, egraph) {
        if depth == n {
            return Some(new_t);
        } else {
            return Some(current);
        }
    }

    map.insert(current, None);

    let eclass = egraph[current].nodes.clone();

    // recursively apply the substitution to all equivalent terms
    // union the result
    // `nid` is the resulting new id
    let egraph_ref = RefCell::new(egraph);
    let nid = eclass
        .iter()
        .filter_map(|l| lambda_subst_aux(&mut egraph_ref.borrow_mut(), map, new_t, depth, l))
        .reduce(|acc, id| {
            egraph_ref.borrow_mut().union(acc, id);
            id
        })?;
    let egraph = egraph_ref.into_inner();

    // update the memoisation map
    let nid = egraph.find(nid);
    map.insert(current, Some(nid));

    Some(nid)
}

/// Helper function for `lambda_subst`.
///
/// Apply the substitution on the top level if it feels like it
fn lambda_subst_aux<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    map: &mut FxHashMap<Id, Option<Id>>,
    new_t: Id,
    depth: usize,
    f @ Lang { head, args }: &Lang,
) -> Option<Id> {
    trace!(
        "in lambda_subst_aux with {depth:}:\n{}",
        f.as_recexpr(egraph).pretty(100)
    );

    let mut args = args.iter();

    if head == &EXISTS || head == &FIND_SUCH_THAT {
        let sorts = *args.next().unwrap();
        let n = list::try_get_egraph(egraph, sorts).unwrap().len();
        let nids: Option<Vec<_>> = args
            .map(|&id| lambda_subst(egraph, map, new_t, depth + n, id))
            .collect();
        Some(egraph.add(head.app_id(chain![[sorts], nids?])))
    } else if head == &LAMBDA_S && depth > 0 {
        lambda_subst(egraph, map, new_t, depth - 1, *args.next().unwrap())
    } else if head == &LAMBDA_O && depth == 0 {
        unreachable!("should have be caught before");
    } else if lambda_substable_fun(head) {
        let nids: Option<Vec<_>> = args
            .map(|&id| lambda_subst(egraph, map, new_t, depth, id))
            .collect();
        Some(egraph.add(head.app_id(nids?)))
    } else {
        None
    }
}

fn lambda_substable_fun(head: &Function) -> bool {
    // !head.flags.intersects(
    //     FunctionFlags::PROLOG_ONLY | FunctionFlags::SMT_ONLY | FunctionFlags::LIST_FA_CONSTR,
    // ) || (head == &LAMBDA_O)
    //     || (head == &LAMBDA_S)
    //     || head.flags.contains(FunctionFlags::LIST_CONSTR)
    head.is_ok_for_substitution()
}

fn get_variable_n<N: Analysis<Lang>>(mut id: Id, egraph: &EGraph<Lang, N>) -> Option<usize> {
    let mut map = Vec::new();

    while !map.contains(&id)
        && let Some(Lang { head, args }) = egraph[id]
            .nodes
            .iter()
            .find(|l| l.head == LAMBDA_O || l.head == LAMBDA_S)
    {
        trace!("check var for:\n\t{}", egraph.id_to_expr(id).pretty(100));
        ereturn_if!(head == &LAMBDA_O, Some(map.len()));
        map.push(id);
        id = args[0];
    }
    None
}
