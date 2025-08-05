//! definition of the `subst` rewrite rules
//!
//! ```text
//! subst(m, x, y) -> m[x -> y]
//! ```

use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::collections::{HashSet, VecDeque};
use std::fmt::format;
use std::mem;
use std::rc::Rc;

use egg::{Analysis, EGraph, Id, Language, Pattern, RecExpr, Searcher, Var};
use golgge::{Dependancy, Rule};
use indexmap::IndexMap;
use itertools::{Itertools, izip};
use logic_formula::egg::SimpleDiscriminant;
use rustc_hash::{FxHashMap, FxHashSet};
use static_init::dynamic;
use utils::transposer::VecTranspose;
use utils::{econtinue_let, ereturn_let};

use crate::problem::PAnalysis;
// use crate::rules::base_rules::substitution;
use crate::rules::utils::mk_subst_rw;
use crate::terms::{MACRO_EXEC, MACRO_FRAME, PRED, SUBSTITUTION, SUBSTITUTION_RULE};
use crate::{Lang, rexp};

declare_trace!($"substitution");

#[dynamic]
static SUBSTITUTION_RULE_PATTERN: Pattern<Lang> = {
    let ast = rexp!((SUBSTITUTION_RULE #0)).to_vec();
    RecExpr::from(ast).into()
};

#[dynamic]
static SUBSTITUTION_PATTERN: Pattern<Lang> = {
    let ast = rexp!((SUBSTITUTION #0 #1 #2)).to_vec();
    RecExpr::from(ast).into()
};

#[dynamic]
static ACCEPTABLY_EMPTY: Vec<Pattern<Lang>> = {
    vec![
        rexp!((MACRO_EXEC (PRED #0) #1)).into_iter().collect(),
        rexp!((MACRO_FRAME (PRED #0) #1)).into_iter().collect(),
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
    fn name(&self) -> std::borrow::Cow<'_, str> {
        "substitution".into()
    }

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
                let [m, x, y] = [0, 1, 2].map(|i| *s.get(Var::from_u32(i as u32)).unwrap());
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

                let g = *s.get(Var::from_u32(0)).unwrap();
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

struct Substitution<'a, N>
where
    N: Analysis<Lang>,
{
    egraph: &'a mut EGraph<Lang, N>,
    x: Id,
    y: Id,
}

impl<'a, N: Analysis<Lang>> Substitution<'a, N> {
    pub fn apply_subst(&mut self) {
        let mut susbts = self
            .egraph
            .classes_for_op(&SUBSTITUTION)
            .into_iter()
            .flatten()
            .flat_map(|id| {
                let tmp = &self;
                tmp.egraph[id]
                    .nodes
                    .iter()
                    .filter_map(move |l| tmp.matches(l).map(|inner_id| (id, inner_id)))
            })
            .collect_vec();

        let mut closure = self.extract_closure(&mut susbts);
        self.sort_closure(&mut closure);
        let new_ids = self.rebuild_closure(&closure);

        // merge subst eclasses
        for (sid, inner_id) in susbts.into_iter().unique() {
            if let Some(nids) = new_ids.get(&sid) {
                for &nid in nids.iter().filter(|&&nid| sid != nid) {
                    self.egraph.union_trusted(sid, nid, "substitution");
                }
            } else {
                // then sid doesn't depend on x in anyway, so substitution does nothing
                self.egraph.union_trusted(sid, inner_id, "nop substitution");
            }
        }
    }

    fn matches(&self, l: &Lang) -> Option<Id> {
        (l.discriminant() == SUBSTITUTION && l.children()[1] == self.x && l.children()[2] == self.y)
            .then(|| l.children()[0])
    }

    /// Extract the closure of [Self::x] in [Self::egraph], while singleing out
    /// the eclass with the right subst using `subst`
    fn extract_closure(&self, susbts: &mut Vec<(Id, Id)>) -> IndexMap<Id, Vec<Lang>> {
        let mut todo: VecDeque<_> = self.egraph[self.x]
            .parents()
            .map(|id| self.egraph.find(id))
            .collect();
        let mut done = IndexMap::new();

        while let Some(current) = todo.pop_front() {
            let eclass = &self.egraph[current];
            if let Some(id) = eclass.nodes.iter().find_map(|l| self.matches(l)) {
                susbts.push((current, id));
                continue;
            }

            done.insert(current, eclass.nodes.clone());
            todo.extend(
                eclass
                    .parents()
                    .map(|id| self.egraph.find(id))
                    .filter(|id| id != &self.x && !done.contains_key(id)),
            );
        }
        done
    }

    // makes sure that `closure` has an order that lets us rebuild the egraph
    fn sort_closure(&self, closure: &mut IndexMap<Id, Vec<Lang>>) {
        let mut todo: VecDeque<_> = [self.x].into();
        'outer: while let Some(id) = todo.pop_front() {
            let index = closure.get_index_of(&id);
            dbg!(&index);
            let (mut parents, mut indices): (VecDeque<_>, VecDeque<_>) = self.egraph[id]
                .parents()
                .filter_map(|pid| {
                    let pidx = closure.get_index_of(&pid)?;
                    // we skip what was already dealt with
                    (index.is_none_or(|idx| idx < pidx)).then_some((pid, pidx))
                })
                .unzip();
            todo.reserve(parents.len());
            let mut did_something = false;

            while !parents.is_empty() {
                debug_assert_eq!(index, closure.get_index_of(&id));
                // find the first index in parents of an eclass that doesn't have up edge within the closure
                let Some(i) = parents.iter().enumerate().find_map(|(i, id)| {
                    self.egraph[*id]
                        .nodes
                        .iter()
                        .inspect(|l| {
                            println!("{}", &l.discriminant().name);
                        })
                        .any(|l| {
                            // self.matches(l) ||
                            l.children()
                                .iter()
                                .inspect(|id| println!("{}", self.egraph.id_to_expr(**id)))
                                .all(|cid| {
                                    closure.get_index_of(cid).is_none_or(|i| {
                                        index.is_some_and(|idx| {
                                            dbg!(i);
                                            i <= idx
                                        })
                                    })
                                })
                        })
                        .then_some(i)
                }) else {
                    eprintln!(
                        "{:} cannot be written without loops: {index:?}\nx = {}\ny = {}",
                        self.egraph.id_to_expr(id),
                        self.egraph.id_to_expr(self.x),
                        self.egraph.id_to_expr(self.y)
                    );
                    for (pid, pidx) in izip!(&parents, &indices) {
                        let expr = self.egraph.id_to_expr(*pid);
                        eprintln!("{pidx:} {expr}");
                        for l in &self.egraph[*pid].nodes {
                            let c = l
                                .children()
                                .iter()
                                .map(|cid| closure.get_index_of(cid))
                                .map(|i| format!("{i:?}"))
                                .join(", ");
                            let f = l.discriminant();
                            eprintln!("\t{f}({c})");
                        }
                    }
                    // let parents = parents
                    //     .iter()
                    //     .map(|(id, i)| format!("{i:}: {}", self.egraph.id_to_expr(*id)))
                    //     .join("\n");
                    // panic!(
                    //     "{:} cannot be written without loops: {index:?}\n{parents}\nx = {}\ny = {}",
                    // )
                    assert!(did_something);
                    continue 'outer;
                };

                closure.swap_indices(indices[0], indices[i]);
                parents.swap(0, i);
                // // unswap the indices in the parent array
                // parents[i].1 = parents[0].1;

                // add to todo
                let id = parents.pop_front().unwrap();
                let _ = indices.pop_front();
                todo.push_back(id);
                did_something = true;
            }
        }
    }

    fn rebuild_closure(&mut self, closure: &IndexMap<Id, Vec<Lang>>) -> FxHashMap<Id, Vec<Id>> {
        let mut remap: FxHashMap<Id, Vec<Id>> = [(self.x, [self.y].into_iter().collect())]
            .into_iter()
            .collect();
        remap.extend(closure.keys().cloned().map(|k| (k, Default::default())));
        {
            // ensure x is mapped to y
            let x_class = remap.get_mut(&self.x).unwrap();
            if !x_class.contains(&self.y) {
                x_class.push(self.y);
            }
        }

        // This is incomplete, but we remove "useless" loops
        for (current_id, ls) in closure {
            let cids = remap.get(current_id).unwrap();
            let mut nids = Vec::new();
            for l in ls {
                // [Self::sort_closure] ensures there is at least one element in here
                let args = l
                    .children()
                    .iter()
                    .map(|id| match remap.get(id) {
                        // if there are up edges, then we ignore them
                        Some(ids) => Cow::Borrowed(ids.as_slice()),
                        None => Cow::Owned(vec![*id]),
                    })
                    .collect_vec();
                let fun = l.discriminant();
                let tranposer = VecTranspose::new(&args);
                nids.extend(
                    tranposer
                        .map(|args| self.egraph.add(fun.app_id(args.iter().cloned().cloned()))),
                );
            }
            let nids = nids
                .into_iter()
                .unique()
                .filter(|id| !cids.contains(id))
                .collect_vec();
            remap.get_mut(current_id).unwrap().extend(nids);
        }
        remap
    }
}
