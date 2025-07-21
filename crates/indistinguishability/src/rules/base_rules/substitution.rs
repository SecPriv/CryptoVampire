//! definition of the `subst` rewrite rules
//!
//! ```text
//! subst(m, x, y) -> m[x -> y]
//! ```

use std::borrow::Cow;
use std::collections::{HashSet, VecDeque};
use std::fmt::format;

use egg::{Analysis, EGraph, Id, Language, Pattern, RecExpr, Searcher, Var};
use golgge::{Dependancy, Rule};
use indexmap::IndexMap;
use itertools::{izip, Itertools};
use logic_formula::egg::SimpleDiscriminant;
use rustc_hash::{FxHashMap, FxHashSet};
use static_init::dynamic;
use utils::transposer::VecTranspose;
use utils::{econtinue_let, ereturn_let};

use crate::problem::PAnalysis;
use crate::rules::base_rules::substitution;
use crate::rules::utils::mk_subst_rw;
use crate::terms::{SUBSTITUTION, SUBSTITUTION_RULE};
use crate::{Lang, rexp};

declare_trace!($"substitution");

#[dynamic]
static SUBSTITUTION_RULE_PATTERN: Pattern<Lang> = {
    let ast = rexp!((SUBSTITUTION_RULE #0 #1 #2)).to_vec();
    RecExpr::from(ast).into()
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
        let subst = substs
            .substs
            .into_iter()
            .map(|s| {
                let [g, x, y] = [0, 1, 2].map(|i| *s.get(Var::from_u32(i as u32)).unwrap());
                Substitution { egraph, x, y }.apply_subst();
                [g]
            })
            .collect();

        egraph.clean = false; // <- to force a true rebuild afterward
        subst
    }
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
        let mut todo: VecDeque<_> = self.egraph[self.x].parents().map(|id| self.egraph.find(id)).collect();
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
            let (mut parents, mut indices): (VecDeque<_>, VecDeque<_> )= self.egraph[id]
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
                let Some(i) = parents
                    .iter()
                    .enumerate()
                    .find_map(|(i, id)| {
                        self.egraph[*id]
                            .nodes
                            .iter()
                            .inspect(|l| {println!("{}", &l.discriminant().name);})
                            .any(|l| {
                                // self.matches(l) ||
                                l.children().iter()
                                .inspect(|id| println!("{}", self.egraph.id_to_expr(**id)))
                                .all(|cid| {
                                    closure
                                        .get_index_of(cid)
                                        .is_none_or(|i| index.is_some_and(|idx| { dbg!(i);  i <= idx}))
                                })
                            })
                            .then_some(i)
                    })
                    else {
                        eprintln!("{:} cannot be written without loops: {index:?}\nx = {}\ny = {}",
                                                    self.egraph.id_to_expr(id),
                            self.egraph.id_to_expr(self.x),
                            self.egraph.id_to_expr(self.y));
                        for (pid, pidx) in izip!(&parents, &indices) {
                            let expr = self.egraph.id_to_expr(*pid);
                            eprintln!("{pidx:} {expr}");
                            for l in &self.egraph[*pid].nodes {
                                let c = l.children().iter().map(|cid| closure.get_index_of(cid)).map(|i| format!("{i:?}")).join(", ");
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
