use std::iter::FusedIterator;

use egg::{Analysis, EGraph, Id, Language};
use rustc_hash::FxHashSet;
use utils::{ebreak_if, implvec};

use crate::Lang;
use crate::terms::Function;

pub struct IdEgraphIter<'a, N: Analysis<Lang>, F> {
    current: Vec<Id>,
    egraph: &'a EGraph<Lang, N>,
    memo: FxHashSet<Id>,
    can_have_children: F,
}

impl<'a, N, F> Iterator for IdEgraphIter<'a, N, F>
where
    N: Analysis<Lang>,
    F: FnMut(&Function) -> bool,
{
    type Item = Id;

    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            current,
            egraph,
            memo,
            can_have_children,
        } = self;

        let next = loop {
            let x = current.pop()?;
            ebreak_if!(!memo.contains(&x), x);
        };
        memo.insert(next);

        current.extend(
            egraph[next]
                .iter()
                .filter(|l| can_have_children(&l.head))
                .flat_map(|f| f.children().iter().copied()),
        );
        Some(next)
    }
}

impl<'a, N, F> FusedIterator for IdEgraphIter<'a, N, F>
where
    N: Analysis<Lang>,
    F: FnMut(&Function) -> bool,
{
}

impl<'a, N, F> IdEgraphIter<'a, N, F>
where
    N: Analysis<Lang>,
    F: FnMut(&Function) -> bool,
{
    pub fn into_set(mut self) -> FxHashSet<Id> {
        for _ in self.by_ref() {}
        self.memo
    }
}

pub fn iter_descendants_id<'a, N, F>(
    egraph: &'a EGraph<Lang, N>,
    ancestor: implvec!(Id),
    can_have_children: F,
) -> IdEgraphIter<'a, N, F>
where
    N: Analysis<Lang>,
    F: FnMut(&Function) -> bool,
{
    IdEgraphIter {
        current: ancestor.into_iter().collect(),
        egraph,
        memo: Default::default(),
        can_have_children,
    }
}

pub fn iter_descendants_lang<'a, N, F>(
    egraph: &'a EGraph<Lang, N>,
    ancestor: implvec!(Id),
    can_have_children: F,
) -> impl Iterator<Item = &'a Lang>
where
    N: Analysis<Lang>,
    F: FnMut(&Function) -> bool,
{
    iter_descendants_id(egraph, ancestor, can_have_children).flat_map(|id| egraph[id].nodes.iter())
}
