use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Debug;

use egg::{Analysis, EClass, EGraph, Id, Pattern, Searcher, Subst};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain, izip};
use rustc_hash::FxHashSet;
use static_init::dynamic;
use utils::{econtinue_if, econtinue_let, ereturn_let, implvec};

use crate::problem::PAnalysis;
use crate::terms::{CONS_FA, EQUIV, Function, NIL_FA};
use crate::{Lang, rexp};

decl_vars!(const; HD:Bitstring, TL:Bitstring, U, V, A, B);

#[dynamic]
static PATTERN_LIST: Pattern<Lang> = Pattern::from(&rexp!((CONS_FA #HD #TL)));
#[dynamic]
static PATTERN_FA: Pattern<Lang> = Pattern::from(&rexp!((EQUIV #U #V #A #B)));

/// Checks if the function can be applied for the given function symbol.
fn can_apply_fa(f: &Function) -> bool {
    (!f.is_out_of_term_algebra()) && f.signature.output.support_deduce()
}

pub struct FaRule;

impl<'a> Rule<Lang, PAnalysis<'a>> for FaRule {
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("fa")
    }

    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: Id) -> Dependancy {
        // Get the substitutions that match the pattern for the goal.
        ereturn_let!(let Some(substs) = PATTERN_FA.search_eclass(prgm.egraph(), goal), Dependancy::impossible());

        // find suitable substitutions and arguments
        // we need to collect now, because the egraph will get dirty later
        let mut candidates = Vec::with_capacity(substs.substs.len());
        {
            // immutable `egraph`
            let egraph = prgm.egraph();
            for subst in &substs.substs {
                if let Some(a) = subst.get(A.as_egg())
                    && let Some(b) = subst.get(B.as_egg())
                    // Extract lists for 'a' and 'b', continue if not a list or the lengths don't match
                    && let Some(list_a) = extract_list(egraph, *a)
                    && let Some(list_b) = extract_list(egraph, *b)
                    && list_a.len() != list_b.len()
                {
                    candidates.push((subst, list_a, list_b))
                }
            }
        };

        let mut results = Vec::new();
        {
            // mutable `egraph`
            let egraph = prgm.egraph_mut();
            for (subst, list_a, list_b) in candidates {
                // Collect sets of arguments for creating new expressions.
                let sets = collect_sets(egraph, &list_a, &list_b);
                // Create new expressions and add them to the egraph.
                results.extend(sets.into_iter().map(|args| {
                    let (ia_id, ib_id) = create_lists(egraph, &args);
                    let u = *subst.get(U.as_egg()).unwrap();
                    let v = *subst.get(V.as_egg()).unwrap();
                    egraph.add(EQUIV.app_id([u, v, ia_id, ib_id]))
                }))
            }
        }
        results.into_iter().map(::std::iter::once).collect()
    }
}

/// Extracts a list of ids from the egraph starting from the given id.
fn extract_list<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, init: Id) -> Option<Vec<Id>> {
    ereturn_let!(let None = PATTERN_LIST.search_eclass(egraph, init), Some(vec![init]));

    let mut visited = FxHashSet::default();
    let mut res = Vec::new();
    let mut next = init;
    while !visited.contains(&next) {
        if let Some(matches) = PATTERN_LIST.search_eclass(egraph, next) {
            visited.insert(next);
            let subst = &matches.substs[0];
            res.push(*subst.get(HD.as_egg()).unwrap());
            next = *subst.get(TL.as_egg()).unwrap();
        } else if egraph[next].leaves().any(|n| n.head == NIL_FA) {
            return Some(res);
        } else {
            break;
        }
    }
    None
}

/// Collects sets of arguments for creating new expressions.
fn collect_sets<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    list_a: &[Id],
    list_b: &[Id],
) -> Vec<FxHashSet<(Id, Id)>> {
    let mut sets = Vec::new();
    // Iterate over pairs of elements from list_a and list_b.
    for (i, (ta, tb)) in list_a.iter().zip(list_b.iter()).enumerate() {
        let ea = &egraph[*ta];
        let eb = &egraph[*tb];
        // Find common heads and collect arguments.
        for (f, a_args, b_args) in find_commun_head(ea, eb) {
            // Collect pairs of arguments.
            let args = if f.is_quantifier() {
                todo!()
            } else {
                process_regular_fun(i, list_a, list_b, a_args, b_args)
            };
            econtinue_let!(let Some(args) = args);
            sets.push(args);
        }
    }
    sets
}

fn process_regular_fun(
    i: usize,
    old_args_a: &[Id],
    old_arg_b: &[Id],
    n_args_a: &[Id],
    n_args_b: &[Id],
) -> Option<FxHashSet<(Id, Id)>> {
    let [ia, ib] = [(old_args_a, n_args_a), (old_arg_b, n_args_b)].map(|(old, new)| {
        let old = old
            .iter()
            .enumerate()
            .filter_map(|(j, x)| (i != j).then_some(x));
        chain![old, new].copied()
    });
    Some(izip!(ia, ib).collect())
}

/// Creates lists in the egraph from a set of argument pairs.
fn create_lists<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    args: &FxHashSet<(Id, Id)>,
) -> (Id, Id) {
    // Create lists for the first and second elements of the argument pairs.
    let ia = args.iter().map(|(x, _)| *x);
    let ib = args.iter().map(|(_, x)| *x);
    let ia_id = mk_list(egraph, ia);
    let ib_id = mk_list(egraph, ib);
    (ia_id, ib_id)
}

/// Creates a list in the egraph from a list of terms.
fn mk_list<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    terms: impl IntoIterator<Item = Id>,
) -> Id {
    let init = egraph.add(NIL_FA.app_id([]));
    terms
        .into_iter()
        .fold(init, |acc, t| egraph.add(CONS_FA.app_id([t, acc])))
}

/// Finds common heads between two eclasses.
fn find_commun_head<'a, D: Debug>(
    a: &'a EClass<Lang, D>,
    b: &'a EClass<Lang, D>,
) -> impl Iterator<Item = (&'a Function, &'a [Id], &'a [Id])> {
    a.nodes
        .iter()
        .cartesian_product(b.nodes.iter())
        .filter(|(a, b)| (a.head == b.head) && can_apply_fa(&a.head))
        .map(|(a, b)| (&a.head, a.args.as_slice(), b.args.as_slice()))
}
