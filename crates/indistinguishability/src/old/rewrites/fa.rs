use std::collections::HashMap;
use std::sync::Arc;

use egg::{Applier, Id, Language, RecExpr, Rewrite};
use itertools::{izip, Itertools};
use rustc_hash::FxHashMap;
use utils::implvec;

use crate::formula::{analysis::{Data, DependancyAnalysis, Unionable}, grammar::{self, Op, TA}};


/**
Implements the rule
```text
a ~ a' b ~ b' Dep(a)∩Dep(a')=Dep(b)∩Dep(b')=∅
---------------------------------------------
          f(a, a') ~ f(b, b')
```
*/
#[derive(Debug, Clone, Copy, Default)]
pub struct FaApplier;

fn skip_nth<U>(n: usize, iter: implvec!(U)) -> impl Iterator<Item = U> {
    iter.into_iter()
        .enumerate()
        .filter_map(move |(i, e)| (i != n).then_some(e))
}

impl FaApplier {
    fn apply_2_with_f(
        egraph: &egg::EGraph<TA, DependancyAnalysis>,
        // f: grammar::Op,
        id: usize, /* index in the args */
        args1: &[Id],
        args2: &[Id],
        // id1: Id,
        // id2: Id,
    ) -> bool {
        let dep1 = Data::from_union(
            skip_nth(id, args1)
                .map(|i| egraph[*i].data.nonces())
                .collect(),
        );
        let dep2 = Data::from_union(
            skip_nth(id, args2)
                .map(|i| egraph[*i].data.nonces())
                .collect(),
        );

        {
            let args_valid = skip_nth(id, izip!(args1, args2)).all(|(a, b)| {
                (egraph.lookup(grammar::Op::Equiv.app([a]))
                    == egraph.lookup(grammar::Op::Equiv.app([b])))
                    || (a == b)
            });
            let no_colision1 = egraph[args1[id]].data.nonces().is_disjoint(&dep1);
            let no_colision2 = egraph[args2[id]].data.nonces().is_disjoint(&dep2);
            args_valid && no_colision1 && no_colision2
        }
        // .then_some((f.clone().app(args1), id1, f.clone().app(args2), id2))
    }

    fn group_by_op<'a>(
        egraph: &'a egg::EGraph<TA, DependancyAnalysis>,
        id: &Id,
    ) -> FxHashMap<(grammar::Op, usize), Vec<(Id, &'a [Id])>> {
        let iter = egraph[*id]
            .parents()
            .flat_map(|id| egraph[id].iter().map(move |l| (id, l)))
            .filter(|(_, l)| !l.is_equiv())
            .flat_map(|(lid, l)| {
                l.children().iter().enumerate().filter_map(move |(i, cid)| {
                    (cid == id).then_some((l.op(), i, lid, l.children()))
                })
            });
        let mut hm: FxHashMap<_, Vec<(Id, &[Id])>> = Default::default();
        if let Some(l) = iter.size_hint().1 {
            hm.reserve(l);
        }
        for (f, i, lid, args) in iter {
            let key = (f.clone(), i);
            hm.entry(key)
                .and_modify(|vargs| vargs.push((lid, args)))
                .or_insert_with(|| vec![(lid, args)]);
        }
        hm
    }

    fn apply_2<'a>(
        egraph: &'a egg::EGraph<TA, DependancyAnalysis>,
        t1: Id,
        t2: Id,
    ) -> impl Iterator<Item = (Id, Id)> + 'a {
        let hm1 = Self::group_by_op(egraph, &t1);
        let mut hm2 = Self::group_by_op(egraph, &t2);

        hm1.into_iter()
            .filter_map(move |(k, v1)| hm2.remove(&k).map(|v2| (k, v1, v2)))
            .flat_map(|(k, v1, v2)| {
                v1.into_iter()
                    .cartesian_product(v2)
                    .map(move |(args1, args2)| (k.clone(), args1, args2))
            })
            .filter(move |((_, id), (_, args1), (_, args2))| {
                Self::apply_2_with_f(egraph, *id, args1, args2)
            })
            .map(|(_, (id1, _), (id2, _))| (id1, id2))
    }
}

impl Applier<TA, DependancyAnalysis> for FaApplier {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<TA, DependancyAnalysis>,
        eclass: egg::Id,
        _: &egg::Subst,
        _: Option<&egg::PatternAst<TA>>,
        _: egg::Symbol,
    ) -> Vec<egg::Id> {
        let iter = egraph[eclass]
            .iter()
            .filter(|l| l.is_equiv())
            .map(|l| l.children()[0])
            .combinations_with_replacement(2)
            .filter_map(|v| v.into_iter().collect_tuple())
            .flat_map(|(t1, t2)| Self::apply_2(egraph, t1, t2))
            .collect_vec(); // to free egraph
        iter.into_iter()
            .filter_map(|(t1, t2)| {
                let e1 = egraph.add(Op::Equiv.app([&t1]));
                let e2 = egraph.add(Op::Equiv.app([&t2]));
                egraph.union_trusted(e1, e2, "fa").then_some(e1)
            })
            .collect()
    }
}

pub fn fa_rewrite() -> Rewrite<TA, DependancyAnalysis> {
    Rewrite::new(
        "fa",
        "(equiv ?a)".parse::<egg::Pattern<TA>>().unwrap(),
        FaApplier,
    )
    .unwrap()
}
