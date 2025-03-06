use std::{
    collections::HashSet,
    ptr::{self, NonNull},
    sync::Arc,
    usize,
};

use egg::{Analysis, DidMerge, EGraph, ENodeOrVar, Id, Language, Pattern, Searcher};
use itertools::Itertools;
use rustc_hash::FxHashSet;
use utilities::UnionableIter;
pub use utilities::{Data, Mergeable, Unionable};
use utils::implvec;

use super::{
    grammar::{Op, TA},
    protocol::Protocol,
};

/**
Decide which nonces a term depends on
 */
#[derive(Debug, Clone)]
pub struct DependancyAnalysis {
    nonces: Vec<Pattern<TA>>,
    id_of_nonces: FxHashSet<Id>,
}

pub type TAGraph = EGraph<TA, DependancyAnalysis>;

mod utilities {
    use std::sync::Arc;

    use egg::{Analysis, EGraph, Id, Pattern, Searcher};
    use itertools::{chain, Itertools};
    use rustc_hash::FxHashSet;
    use utils::{ereturn_if, ord_util::sort_by_key};

    use crate::formula::grammar::TA;

    use super::TAGraph;

    pub trait Mergeable<W>: Sized {
        fn merge(&self, other: &Self, with: W) -> Self;

        /**
        checks if the result of [Mergeable::merge] changed to value.

        To be caled after [Mergeable::merge].
         */
        fn has_changed(&self, old_self: &Self) -> bool;
    }

    pub trait MergeableIter<W> {
        type Item;

        fn merge(&mut self, with: W) -> Option<Self::Item>;
    }

    impl<W: Copy, I> MergeableIter<W> for I
    where
        I: Iterator,
        I::Item: Mergeable<W>,
    {
        type Item = I::Item;

        fn merge(&mut self, with: W) -> Option<Self::Item> {
            let init = self.next()?;
            Some(self.fold(init, |acc, e| acc.merge(&e, with)))
        }
    }

    pub trait Unionable: Sized {
        fn union(&self, other: &Self) -> Self;
    }

    pub trait UnionableIter {
        type Item;
        fn union(&mut self) -> Option<Self::Item>;
    }
    impl<'a, I, U> UnionableIter for I
    where
        I: Iterator<Item = &'a U>,
        U: Unionable + 'a,
    {
        type Item = U;

        fn union(&mut self) -> Option<Self::Item> {
            let init = self.next()?;
            let Some(init2) = self.next() else {
                return Some(init.union(init));
            };
            Some(self.fold(init.union(init2), |acc, e| U::union(&acc, e)))
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone, Default)]
    pub struct Data(Arc<FxHashSet<Id>>);

    impl Data {
        pub fn iter<'a>(&'a self) -> impl Iterator<Item = Id> + 'a {
            self.0.iter().copied()
        }

        pub fn is_disjoint(&self, other: &Self) -> bool {
            self.0.is_disjoint(&other.0)
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }
    }

    impl<'a> Mergeable<(&'a TAGraph, Option<&'a [Pattern<TA>]>)> for Data {
        fn merge(
            &self,
            other: &Self,
            (egraph, steps): (&'a TAGraph, Option<&'a [Pattern<TA>]>),
        ) -> Self {
            let (a, b) = sort_by_key(&mut |x: &&Data| x.len(), self, other);
            debug_assert!(a.0.len() <= b.0.len());
            let input_iter = steps.map(|pats| {
                chain!{
                    a.0.iter().filter(|&&id| pats.iter().any(|pat| pat.search_eclass(egraph, id).is_some())),
                    b.0.iter().filter(|&&id| pats.iter().any(|pat| pat.search_eclass(egraph, id).is_some())),
                }
            });
            let set: FxHashSet<_> = chain! {
                a.0.intersection(&b.0),
                input_iter.into_iter().flatten()
            }
            .copied()
            .collect();

            if set.len() == a.0.len() {
                a.clone()
            } else {
                Data(Arc::new(set))
            }
        }

        fn has_changed(&self, old_self: &Self) -> bool {
            self.0.len() != old_self.0.len()
        }
    }

    impl Unionable for Data {
        fn union(&self, other: &Self) -> Self {
            ereturn_if!(Arc::ptr_eq(&self.0, &other.0), self.clone());
            let (a, b) = sort_by_key(&mut |x: &&Data| x.len(), self, other);
            debug_assert!(a.0.len() <= b.0.len());
            if a.0.is_subset(&b.0) {
                b.clone()
            } else {
                Data(Arc::new(a.0.union(&b.0).into_iter().copied().collect()))
            }
        }
    }

    impl FromIterator<Id> for Data {
        fn from_iter<T: IntoIterator<Item = Id>>(iter: T) -> Self {
            Data(Arc::new(iter.into_iter().collect()))
        }
    }
}

#[derive(Debug, Clone)]
pub struct DependancyAnalysisData {
    nonces: Data,
    /** nonce that are not in key position for PRF */
    nonces_prf: Data,
    input: bool,
}

impl Default for DependancyAnalysisData {
    fn default() -> Self {
        Self {
            nonces: Default::default(),
            nonces_prf: Default::default(),
            input: false,
        }
    }
}

impl DependancyAnalysisData {
    #[inline]
    pub fn map_ref_N<'a, const N: usize, F1, F2>(
        selves: [&'a Self; N],
        mut f: F1,
        input_f: F2,
    ) -> Self
    where
        F1: FnMut([&'a Data; N]) -> Data,
        F2: FnOnce([bool; N]) -> bool,
    {
        let nonces = f(selves.map(Self::nonces));
        let nonces_prf = f(selves.map(Self::nonces_prf));
        let input = input_f(selves.map(Self::input));
        Self {
            nonces,
            nonces_prf,
            input,
        }
    }

    pub fn nonces(&self) -> &Data {
        &self.nonces
    }

    pub fn nonces_prf(&self) -> &Data {
        &self.nonces_prf
    }

    pub fn input(&self) -> bool {
        self.input
    }
}

impl FromIterator<Id> for DependancyAnalysisData {
    fn from_iter<T: IntoIterator<Item = Id>>(iter: T) -> Self {
        let data: Data = iter.into_iter().collect();
        Self {
            nonces: data.clone(),
            nonces_prf: data,
            input: false,
        }
    }
}

impl<'a> Mergeable<(&'a TAGraph, &'a [Pattern<TA>])> for DependancyAnalysisData {
    fn merge(&self, other: &Self, (egraph, pats): (&'a TAGraph, &'a [Pattern<TA>])) -> Self {
        let pats = (self.input() || other.input()).then_some(pats);
        Self::map_ref_N(
            [self, other],
            |[d1, d2]| d1.merge(d2, (egraph, pats)),
            |_| pats.is_some(),
        )
    }

    fn has_changed(&self, old_self: &Self) -> bool {
        let Self {
            nonces: ns,
            nonces_prf: nprfs,
            input: si,
        } = self;
        let Self {
            nonces: no,
            nonces_prf: nprfo,
            input: so,
        } = old_self;
        ns.has_changed(no) || nprfs.has_changed(nprfo) || si != so
    }
}

impl Unionable for DependancyAnalysisData {
    fn union(&self, other: &Self) -> Self {
        Self::map_ref_N(
            [self, other],
            |[d1, d2]| d1.union(d2),
            |_| self.input() || other.input(),
        )
    }
}

impl Analysis<TA> for DependancyAnalysis {
    type Data = DependancyAnalysisData;

    fn make(egraph: &mut egg::EGraph<TA, Self>, enode: &TA) -> Self::Data {
        match enode.op() {
            Op::Nonce => {
                let id = enode.children()[0];
                if !egraph.analysis.id_of_nonces.contains(&id)
                    && egraph
                        .analysis
                        .nonces
                        .iter()
                        .any(|pat| pat.search_eclass(egraph, id).is_some())
                {
                    egraph.analysis.id_of_nonces.insert(id);
                }

                [id].into_iter()
                    // .map(IdOrInput::from_id)
                    .collect()
            }
            Op::Input => DependancyAnalysisData {
                input: true,
                ..Default::default()
            },
            Op::Equiv => Default::default(),
            Op::Hash => Self::Data {
                nonces: // Unionable::from_union(
                    enode
                        .children()
                        .iter()
                        .map(|i| egraph[*i].data.nonces())
                        .union().unwrap(),
                nonces_prf: Default::default(),
                input: false,
            },
            _ => enode
                .children()
                .iter()
                .map(|i| &egraph[*i].data)
                .union()
                .unwrap(),
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        let na = a.merge(&b);
        let didm = egg::DidMerge(na.has_changed(a), na.has_changed(&b));
        *a = na;
        didm
    }
}

/*
   Here we expect variables to *only* point to indices.
   If this assumption doesn't hold, then the rest is unsound
*/
impl Analysis<ENodeOrVar<TA>> for DependancyAnalysis {
    type Data = DependancyAnalysisData;

    fn make(egraph: &mut egg::EGraph<ENodeOrVar<TA>, Self>, enode: &ENodeOrVar<TA>) -> Self::Data {
        let ENodeOrVar::ENode(enode) = enode else {
            // I love rust
            return Default::default();
        };
        match enode.op() {
            Op::Nonce => [enode.children()[0]]
                .into_iter()
                .map(IdOrInput::from_id)
                .collect(),
            Op::Input => [enode.children()[0]]
                .into_iter()
                .map(IdOrInput::from_input_arg)
                .collect(),
            Op::Equiv => Default::default(),
            Op::Hash => Self::Data {
                nonces: Unionable::from_union(
                    enode
                        .children()
                        .iter()
                        .map(|i| egraph[*i].data.nonces())
                        .collect(),
                ),
                nonces_prf: Default::default(),
            },
            _ => {
                Self::Data::from_union(enode.children().iter().map(|i| &egraph[*i].data).collect())
            }
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        let na = a.merge(&b);
        let didm = egg::DidMerge(na.has_changed(a), na.has_changed(&b));
        *a = na;
        didm
    }
}
