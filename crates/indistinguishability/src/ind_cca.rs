//! IND-CCA2 axioms
//!
//! TODO: make it IND-CCA1

use std::{collections::VecDeque, hash::Hash, iter::FusedIterator};

use egg::{EGraph, Id, Language, RecExpr};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{is_nonce, Rule, CCSA};

#[derive(Debug, Clone, Default)]
struct SearchState(FxHashMap<Id, IdSearchState>);

#[derive(Debug, Clone)]
struct IdSearchState(FxHashSet<Id>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum SStatus {
    Searching,
    Found,
    NotFound,
}

impl From<SStatus> for bool {
    fn from(value: SStatus) -> Self {
        match value {
            SStatus::Searching | SStatus::Found => false,
            SStatus::NotFound => true,
        }
    }
}

impl From<bool> for SStatus {
    fn from(value: bool) -> Self {
        if value {
            SStatus::NotFound
        } else {
            SStatus::Found
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum SearchKind {
    Randomness,
    KeyBeforeEnc,
    KeyAfterEnc,
}

impl SearchKind {
    pub fn is_key(self) -> bool {
        match self {
            SearchKind::KeyAfterEnc | SearchKind::KeyBeforeEnc => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Default)]
struct SubtermDownMemoize(FxHashMap<Id, SStatus>);

/// Early return macro, works with named blocks and regular returns
///
/// # Example
/// ```rust
/// let test = 'a : {
///   break_if!('a, 1 == 2, 1);
///   break_if!('a, true, 2);
///   break_if!('a, true, 3);
///   4
/// };
/// assert_eq(test, 2)
/// ```
macro_rules! ereturn_if {
    ($label:lifetime, $value:expr, $ret:expr) => {
        if $value {
          break $label $ret
        }
    };
    ($value:expr, $ret:expr) => {
        if $value {
          return $ret
        }
    };
    ($label:lifetime, $value:expr) => {
        ereturn_if!($label, $value, ())
    };
    ($value:expr) => {
        ereturn_if!($value, ())
    };
}

fn not_subterm_down<'a>(
    egraph: &'a EGraph<CCSA, ()>,
    memoize: &mut SubtermDownMemoize,
    kind: SearchKind,
    ignore: &[Id],
    nonce: Id,
    term: Id,
) -> bool {
    match memoize.0.get(&term) {
        Some(SStatus::Found) | Some(SStatus::Searching) => false,
        Some(SStatus::NotFound) => true,
        None => {
            let result = 'res: {
                // base cases
                ereturn_if!('res, term == nonce, false);
                ereturn_if!('res, ignore.contains(&term), true);

                // recurse
                memoize.0.insert(term, SStatus::Searching);

                fn find_next(kind: SearchKind, k: Id, t: &CCSA) -> impl Iterator<Item = &Id> {
                    match (t, kind) {
                        (CCSA::Dec(args), SearchKind::KeyBeforeEnc) if args[1] == k => {
                            args[..1].iter()
                        }
                        (CCSA::Pk(k2), kind) if (kind.is_key() && k2 == &k) => [].iter(),
                        (CCSA::Input(_), _) => [].iter(), // TODO
                        _ => t.children().iter(),
                    }
                }

                let eclass = &egraph[term];

                eclass.iter().any(|term| {
                    find_next(kind, nonce, term)
                        .all(|&id| not_subterm_down(egraph, memoize, kind, ignore, nonce, id))
                })
            };
            memoize
                .0
                .entry(term)
                .and_modify(|e| *e = result.into())
                .or_insert(result.into());
            result
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Instance {
    /// message
    m: Id,
    /// key
    k: Id,
    /// randomness
    r: Id,
    /// `enc(m, r, pk(k))`
    c: Id,
}

#[derive(Debug, Clone)]
struct Searcher<'a> {
    egraph: &'a EGraph<CCSA, ()>,
    todos: FxHashMap<Id, RecExpr<CCSA>>,
    done: FxHashSet<Id>,
    memoize_key: SubtermDownMemoize,
    memoize_rand: SubtermDownMemoize,
    instance: Instance,
}

impl<'a> PartialEq for Searcher<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.instance == other.instance
    }
}

impl<'a> Eq for Searcher<'a> {}

impl<'a> Hash for Searcher<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.instance.hash(state);
    }
}

impl<'a> Searcher<'a> {
    fn search_up_once(&mut self, l: &'a CCSA, id: Id, rec_expr: &RecExpr<CCSA>) {
        let Self {
            egraph,
            memoize_key,
            memoize_rand,
            instance: Instance { k, r, c, .. },
            ..
        } = self;
        let ignore = &[*c];
        let mut is_sibling_valid = |sibling: Id| {
            use SearchKind::*;
            not_subterm_down(egraph, memoize_key, KeyBeforeEnc, ignore, *k, sibling)
                && not_subterm_down(egraph, memoize_rand, Randomness, ignore, *r, sibling)
        };
        if l.all(|sibling| sibling == id || is_sibling_valid(sibling)) {
            let rec_expr = l.join_recexprs(|s_id| {
                if s_id == id {
                    rec_expr.clone()
                } else {
                    egraph.id_to_expr(s_id)
                }
            });
            self.push(id, rec_expr);
        }
    }

    fn pop(&mut self) -> Option<(Id, RecExpr<CCSA>)> {
        let (nxt, rec_expr) = self.todos.iter().next()?;
        let (nxt, rec_expr) = (*nxt, rec_expr.clone());
        self.todos.remove(&nxt).unwrap();
        self.done.insert(nxt);
        Some((nxt, rec_expr))
    }

    fn push(&mut self, id: Id, rec_expr: RecExpr<CCSA>) {
        ereturn_if!(self.done.contains(&id));
        self.todos.insert(id, rec_expr);
    }
}

impl<'a> Iterator for Searcher<'a> {
    type Item = (Id, RecExpr<CCSA>);

    fn next(&mut self) -> Option<Self::Item> {
        let (current, rec_expr) = self.pop()?;
        let eclass = &self.egraph[current];

        ereturn_if!(
            eclass.iter().any(|t| t.is_equiv()),
            Some((current, rec_expr))
        );

        eclass
            .parents()
            .for_each(|(l, id)| self.search_up_once(l, id, &rec_expr));
        self.next()
    }
}

impl<'a> FusedIterator for Searcher<'a> {}

impl Instance {
    pub fn into_search(self, egraph: &EGraph<CCSA, ()>) -> Option<Searcher<'_>> {
        let Instance { m, k, r, c } = &self;
        use SearchKind::*;
        let mut memoize_key = Default::default();
        let mut memoize_rand = Default::default();

        if k != r
            && is_nonce(egraph, *k)
            && is_nonce(egraph, *r)
            && not_subterm_down(egraph, &mut memoize_key, KeyBeforeEnc, &[], *k, *m)
            && not_subterm_down(egraph, &mut memoize_rand, Randomness, &[], *r, *m)
        {
            let rec_expr = {
                let default_id = Default::default();
                let len = CCSA::Length(default_id).join_recexprs(|_| egraph.id_to_expr(*m));
                let zs = CCSA::Zeroes(default_id).join_recexprs(|_| len.clone());
                let pk = CCSA::Pk(0.into()).join_recexprs(|_| egraph.id_to_expr(*k));

                CCSA::Enc([0.into(), 1.into(), 2.into()]).join_recexprs(|id| {
                    if id == 0.into() {
                        zs.clone()
                    } else if id == 1.into() {
                        egraph.id_to_expr(*r)
                    } else {
                        pk.clone()
                    }
                })
            };
            Some(Searcher {
                egraph,
                todos: [(*c, rec_expr)].into_iter().collect(),
                done: Default::default(),
                memoize_key,
                memoize_rand,
                instance: self,
            })
        } else {
            None
        }
    }

    // pub fn from_id(egraph: &'a EGraph<CCSA, ()>, id:Id) -> impl Iterator<Item = Self> {

    // }
}

fn find_searchs(egraph: &EGraph<CCSA, ()>) -> impl Iterator<Item = Searcher<'_>> {
    let pattern: egg::Pattern<CCSA> = "(enc ?m ?r (pk ?k))".parse().unwrap();
    let [m_v, r_v, k_v]: [egg::Var; 3] = ["?m", "?r", "?k"].map(|str| str.parse().unwrap());
    let instances = egg::Searcher::search(&pattern, egraph)
        .into_iter()
        .flat_map(|egg::SearchMatches { eclass, substs, .. }| {
            substs.into_iter().map(move |subst| (eclass, subst))
        })
        .map(move |(eclass, subst)| Instance {
            c: eclass,
            m: *subst.get(m_v).unwrap(),
            r: *subst.get(r_v).unwrap(),
            k: *subst.get(k_v).unwrap(),
        })
        .unique()
        .collect_vec();
    instances
        .into_iter()
        .filter_map(|instance| instance.into_search(egraph))
}

#[derive(Debug, Clone, Copy)]
pub struct IndCCA2;
impl Rule<CCSA, ()> for IndCCA2 {
    type T = RecExpr<CCSA>;

    fn find(&self, egraph: &EGraph<CCSA, ()>) -> impl Iterator<Item = crate::Union<Self::T>> {
        find_searchs(egraph).flatten().map(|(id, t)| crate::Union {
            old: id,
            new: t,
            reason: "ind-cca2".into(),
        })
    }
}
