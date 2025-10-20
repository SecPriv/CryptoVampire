use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Debug;

use egg::{Analysis, EClass, EGraph, Id, Pattern, Searcher, Subst};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, izip};
use rustc_hash::FxHashSet;
use static_init::dynamic;
use utils::{ereturn_let, implvec};

use crate::problem::PAnalysis;
use crate::terms::{CONS_FA, EQUIV, Function, NIL_FA};
use crate::{Lang, rexp};

decl_vars!(const; HD:Bitstring, TL:Bitstring, U, V, A, B);

#[dynamic]
static PATTERN_LIST: Pattern<Lang> = Pattern::from(&rexp!((CONS_FA #HD #TL)));

#[dynamic]
static PATTERN_FA: Pattern<Lang> = Pattern::from(&rexp!((EQUIV #U #V #A #B)));

fn extract_list<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, init: Id) -> Option<Vec<Id>> {
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

fn mk_list<N: Analysis<Lang>>(egraph: &mut EGraph<Lang, N>, terms: implvec!(Id)) -> Id {
    let init = egraph.add(NIL_FA.app_id([]));

    terms
        .into_iter()
        .fold(init, |acc, t| egraph.add(CONS_FA.app_id([t, acc])))
}

fn can_apply_fa(f: &Function) -> bool {
    (!f.is_out_of_term_algebra()) && f.signature.output.support_deduce()
}

fn find_commun_head<'a, D: Debug>(
    a: &'a EClass<Lang, D>,
    b: &'a EClass<Lang, D>,
) -> impl Iterator<Item = (&'a [Id], &'a [Id])> {
    a.nodes
        .iter()
        .cartesian_product(b.nodes.iter())
        .filter(|(a, b)| (a.head == b.head) && can_apply_fa(&a.head))
        .map(|(a, b)| (a.args.as_slice(), b.args.as_slice()))
}

// ----------------------------------------------------------------------------
// --- Refactored Implementation ----------------------------------------------
// ----------------------------------------------------------------------------

pub struct FaRule;

impl<'a> Rule<Lang, PAnalysis<'a>> for FaRule {
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("fa")
    }

    fn search(
        &self,
        prgm: &mut golgge::Program<Lang, PAnalysis<'a>>,
        goal: Id,
    ) -> golgge::Dependancy {
        // 1. Find initial matches for the main pattern
        let matches = match PATTERN_FA.search_eclass(prgm.egraph(), goal) {
            Some(m) => m,
            None => return Dependancy::impossible(),
        };

        let egraph_refcell = RefCell::new(prgm.egraph_mut());
        let mut all_applications = Vec::new();

        // 2. Loop over each potential substitution
        for subst in &matches.substs {
            // This function now contains the core logic for a single match
            let applications = process_substitution(subst, &egraph_refcell);
            all_applications.extend(applications);
        }

        all_applications.into_iter().collect()
    }
}

/// Processes a single substitution match, generating all possible new goals.
fn process_substitution<'a>(
    subst: &Subst,
    egraph_refcell: &RefCell<&mut EGraph<Lang, PAnalysis<'a>>>,
) -> Vec<[Id; 1]> {
    // 3. Extract variables and the corresponding lists from the e-graph
    let Some(a) = subst.get(A.as_egg()).copied() else { return vec![]; };
    let Some(b) = subst.get(B.as_egg()).copied() else { return vec![]; };

    let list_a;
    let list_b;
    {
        // Borrow the e-graph immutably to read data
        let egraph = egraph_refcell.borrow();
        list_a = match extract_list(&egraph, a) {
            Some(la) => la,
            None => return vec![],
        };
        list_b = match extract_list(&egraph, b) {
            Some(lb) => lb,
            None => return vec![],
        };
    } // Immutable borrow is dropped here

    // 4. Ensure lists are of the same length
    if list_a.len() != list_b.len() {
        return vec![];
    }

    // 5. Generate argument sets based on common function heads within the lists
    let new_arg_sets = generate_argument_sets(&list_a, &list_b, &egraph_refcell.borrow());

    // 6. Build the final goals from the generated argument sets
    let mut applications = Vec::new();
    for arg_set in new_arg_sets {
        // Borrow mutably to add new terms to the e-graph
        let mut egraph = egraph_refcell.borrow_mut();
        let new_goal = build_new_goal(subst, arg_set, &mut egraph);
        applications.push([new_goal]);
    }
    applications
}

/// Iterates through two lists to find pairs of elements with common function heads
/// and generates new argument lists based on them.
fn generate_argument_sets<'a>(
    list_a: &[Id],
    list_b: &[Id],
    egraph: &EGraph<Lang, PAnalysis<'a>>,
) -> Vec<HashSet<(Id, Id)>> {
    let mut result_sets = Vec::new();

    // Loop through corresponding elements of both lists
    for (i, (term_a, term_b)) in izip!(list_a, list_b).enumerate() {
        let eclass_a = &egraph[*term_a];
        let eclass_b = &egraph[*term_b];

        // Find all function applications with the same head in both e-classes
        for (head_args_a, head_args_b) in find_commun_head(eclass_a, eclass_b) {
            assert_eq!(head_args_a.len(), head_args_b.len());

            // Reconstruct the argument lists:
            // - Take all elements from the original list *except* the one at index `i`.
            // - Append the arguments from the common head found.
            let new_args_a = list_a.iter().enumerate()
                .filter_map(|(j, x)| (i != j).then_some(*x))
                .chain(head_args_a.iter().cloned());

            let new_args_b = list_b.iter().enumerate()
                .filter_map(|(j, x)| (i != j).then_some(*x))
                .chain(head_args_b.iter().cloned());
            
            // Collect the new pairs into a HashSet to ensure uniqueness
            let args: HashSet<_> = izip!(new_args_a, new_args_b).collect();
            result_sets.push(args);
        }
    }
    result_sets
}

/// Builds the final `EQUIV` term in the e-graph using a set of new arguments.
fn build_new_goal<N: Analysis<Lang>>(
    subst: &Subst,
    args: HashSet<(Id, Id)>,
    egraph: &mut EGraph<Lang, N>,
) -> Id {
    // Create the two new lists in the e-graph
    let new_list_a = mk_list(egraph, args.iter().map(|(x, _)| *x));
    let new_list_b = mk_list(egraph, args.iter().map(|(_, y)| *y));

    // Get the universal quantifiers U and V from the original substitution
    let u = *subst.get(U.as_egg()).unwrap();
    let v = *subst.get(V.as_egg()).unwrap();

    // Add the new goal term to the e-graph
    egraph.add(EQUIV.app_id([u, v, new_list_a, new_list_b]))
}
