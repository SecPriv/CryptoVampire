use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Debug;

use egg::{Analysis, EClass, EGraph, Id, Pattern, Searcher};
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
        ereturn_let!(let Some(substs)= PATTERN_FA.search_eclass(prgm.egraph(), goal), Dependancy::impossible());

        let egraph_refcell = RefCell::new(prgm.egraph_mut());

        substs
            .substs
            .iter()
            .filter_map(|subst| {
                let a = *subst.get(A.as_egg())?;
                let b = *subst.get(B.as_egg())?;
                let egraph = egraph_refcell.borrow();
                let list_a = extract_list(&egraph, a)?;
                let list_b = extract_list(&egraph, b)?;
                Some((subst, list_a, list_b))
            })
            .filter(|(_, l1, l2)| l1.len() == l2.len())
            .flat_map(|(subst, la, lb)| {
                let egraph = egraph_refcell.borrow();
                let sets = izip!(&la, &lb)
                    .enumerate()
                    .flat_map(|(i, (ta, tb))| {
                        let ea = &egraph[*ta];
                        let eb = &egraph[*tb];
                        find_commun_head(ea, eb).map(move |(a, b)| (i, a, b))
                    })
                    .map(|(i, a, b)| {
                        assert_eq!(a.len(), b.len());
                        let ia = la
                            .iter()
                            .enumerate()
                            .filter_map(|(j, x)| (i != j).then_some(x))
                            .chain(a)
                            .cloned();
                        let ib = lb
                            .iter()
                            .enumerate()
                            .filter_map(|(j, x)| (i != j).then_some(x))
                            .chain(b)
                            .cloned();
                        let args: HashSet<_> = izip!(ia, ib).collect();
                        args
                    })
                    .collect_vec();

                sets.into_iter().map(|args| {
                    let mut egraph = egraph_refcell.borrow_mut();
                    let ia = mk_list(&mut egraph, args.iter().map(|(x, _)| *x));
                    let ib = mk_list(&mut egraph, args.iter().map(|(_, x)| *x));

                    let u = *subst.get(U.as_egg()).unwrap();
                    let v = *subst.get(V.as_egg()).unwrap();

                    [egraph.add(EQUIV.app_id([u, v, ia, ib]))]
                })
            })
            .collect()
    }
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
