use std::{collections::HashSet, ptr::NonNull, sync::Arc, usize};

use egg::{Analysis, DidMerge, EGraph, ENodeOrVar, Id, Language, Pattern};
use itertools::Itertools;
use rustc_hash::FxHashSet;
use utilities::IdOrInput;
pub use utilities::{Data, Mergeable, Unionable};
use utils::implvec;

use super::{grammar::{Op, TA}, protocol::Protocol};

/**
Decide which nonces a term depends on
 */
#[derive(Debug,  Clone, )]
pub struct DependancyAnalysis {
    nonces: Vec<Pattern<TA>>,
}

mod utilities {
    use std::sync::Arc;

    use egg::{Analysis, EGraph, Id};
    use itertools::Itertools;
    use rustc_hash::FxHashSet;
    use utils::ord_util::sort_by_key;

    use crate::formula::grammar::TA;

    pub trait Mergeable: Sized {
        fn merge(&self, other: &Self) -> Self;

        /**
        checks if the result of [Mergeable::merge] changed to value.

        To be caled after [Mergeable::merge].
         */
        fn has_changed(&self, old_self: &Self) -> bool;

        fn from_merge(x: Merge<Self>) -> Self {
            x.0
        }
    }

    #[derive(Debug, Default)]
    pub struct Merge<U>(pub U);

    impl<'a, U> FromIterator<&'a U> for Merge<U>
    where
        U: Mergeable + Default + Sized + Clone,
    {
        fn from_iter<T: IntoIterator<Item = &'a U>>(iter: T) -> Self {
            let mut iter = iter.into_iter();
            let fst = iter.next().cloned().unwrap_or_default();
            Merge(iter.into_iter().fold(fst, |a, b| a.merge(b)))
        }
    }

    pub trait Unionable: Sized {
        fn union(&self, other: &Self) -> Self;

        fn from_union(x: Union<Self>) -> Self {
            x.0
        }
    }

    #[derive(Debug, Default)]
    pub struct Union<U>(pub U);

    impl<'a, U> FromIterator<&'a U> for Union<U>
    where
        U: Unionable + Default + Sized + Clone,
    {
        fn from_iter<T: IntoIterator<Item = &'a U>>(iter: T) -> Self {
            let mut iter = iter.into_iter();
            let fst = iter.next().cloned().unwrap_or_default();
            Union(iter.into_iter().fold(fst, |a, b| a.union(b)))
        }
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
    pub enum IdOrInput {
        Id(Id),
        Input(Id),
    }

    impl IdOrInput {
        pub fn id(&self) -> Id {
            match self {
                IdOrInput::Id(id) | IdOrInput::Input(id) => *id,
            }
        }

        /// Returns `true` if the id or input is [`Input`].
        ///
        /// [`Input`]: IdOrInput::Input
        #[must_use]
        pub fn is_input(&self) -> bool {
            matches!(self, Self::Input(..))
        }

        pub fn from_input_arg(id: Id) -> Self {
            Self::Input(id)
        }

        pub fn from_id(id: Id) -> Self {
            Self::Id(id)
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone, Default)]
    pub struct Data(Arc<FxHashSet<IdOrInput>>);

    impl Data {
        pub fn iter<'a>(&'a self) -> impl Iterator<Item = IdOrInput> + 'a {
            self.0.iter().copied()
        }

        pub fn is_disjoint(&self, other: &Self) -> bool {
            self.0.is_disjoint(&other.0)
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }
    }

    impl Mergeable for Data {
        fn merge(&self, other: &Self) -> Self {
            let (a, b) = sort_by_key(&mut |x: &&Data| x.len(), self, other);
            debug_assert!(a.0.len() <= b.0.len());
            if a.0.is_subset(&b.0) {
                a.clone()
            } else {
                Data(Arc::new(a.0.intersection(&b.0).cloned().collect()))
            }
        }

        fn has_changed(&self, old_self: &Self) -> bool {
            self.0.len() != old_self.0.len()
        }
    }

    impl Unionable for Data {
        fn union(&self, other: &Self) -> Self {
            let (a, b) = sort_by_key(&mut |x: &&Data| x.len(), self, other);
            debug_assert!(a.0.len() <= b.0.len());
            if a.0.is_subset(&b.0) {
                b.clone()
            } else {
                Data(Arc::new(a.0.union(&b.0).into_iter().copied().collect()))
            }
        }
    }

    impl FromIterator<IdOrInput> for Data {
        fn from_iter<T: IntoIterator<Item = IdOrInput>>(iter: T) -> Self {
            Self(Arc::new(iter.into_iter().collect()))
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct DependancyAnalysisData {
    nonces: Data,
    /** nonce that are not in key position for PRF */
    nonces_prf: Data,
    input: bool
}

impl DependancyAnalysisData {
    // #[inline]
    // pub fn map_ref_N<'a, const N: usize, F: FnMut([&'a Data; N]) -> Data>(
    //     selves: [&'a Self; N],
    //     f: &mut F,
    // ) -> Self {
    //     let nonces = f(selves.map(|Self { nonces, .. }| nonces));
    //     let nonces_prf = f(selves.map(|Self { nonces_prf, .. }| nonces_prf));
    //     Self { nonces, nonces_prf }
    // }

    pub fn nonces(&self) -> &Data {
        &self.nonces
    }

    pub fn nonces_prf(&self) -> &Data {
        &self.nonces_prf
    }
}

impl FromIterator<IdOrInput> for DependancyAnalysisData {
    fn from_iter<T: IntoIterator<Item = IdOrInput>>(iter: T) -> Self {
        let data: Data = iter.into_iter().collect();
        Self {
            nonces: data.clone(),
            nonces_prf: data,
        }
    }
}

impl Mergeable for DependancyAnalysisData {
    fn merge(&self, other: &Self) -> Self {
        Self::map_ref_N([self, other], &mut |[d1, d2]| d1.merge(d2))
    }

    fn has_changed(&self, old_self: &Self) -> bool {
        let Self {
            nonces: ns,
            nonces_prf: nprfs,
            input: si
        } = self;
        let Self {
            nonces: no,
            nonces_prf: nprfo,
            input: so
        } = old_self;
        ns.has_changed(no) || nprfs.has_changed(nprfo) || si != so
    }
}

impl Unionable for DependancyAnalysisData {
    fn union(&self, other: &Self) -> Self {
        Self::map_ref_N([self, other], &mut |[d1, d2]| d1.union(d2))
    }
}

impl Analysis<TA> for DependancyAnalysis {
    type Data = DependancyAnalysisData;

    fn make(egraph: &mut egg::EGraph<TA, Self>, enode: &TA) -> Self::Data {
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
