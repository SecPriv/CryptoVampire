use std::iter::FusedIterator;

use egg::{Analysis, EGraph, Id, Language};
use rustc_hash::FxHashSet;
use utils::ebreak_if;

use crate::Lang;

struct IdEgraphIter<'a, N: Analysis<Lang>> {
    current: Vec<Id>,
    egraph: &'a EGraph<Lang, N>,
    memo: FxHashSet<Id>,
}

impl<'a, N: Analysis<Lang>> Iterator for IdEgraphIter<'a, N> {
    type Item = Id;

    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            current,
            egraph,
            memo,
        } = self;

        let next = loop {
            let x = current.pop()?;
            ebreak_if!(!memo.contains(&x), x);
        };
        memo.insert(next);

        current.extend(
            egraph[next]
                .iter()
                .flat_map(|f| f.children().iter().copied()),
        );
        Some(next)
    }
}

impl<'a, N: Analysis<Lang>> FusedIterator for IdEgraphIter<'a, N> {}

pub fn iter_descendants_id<'a, N: Analysis<Lang>>(
    egraph: &'a EGraph<Lang, N>,
    ancestor: Id,
) -> impl Iterator<Item = Id> + use<'a, N> {
    IdEgraphIter {
        current: vec![ancestor],
        egraph,
        memo: Default::default(),
    }
}

pub fn iter_descendants_lang<'a, N: Analysis<Lang>>(
    egraph: &'a EGraph<Lang, N>,
    ancestor: Id,
) -> impl Iterator<Item = &'a Lang> + use<'a, N> {
    iter_descendants_id(egraph, ancestor).flat_map(|id| egraph[id].nodes.iter())
}
