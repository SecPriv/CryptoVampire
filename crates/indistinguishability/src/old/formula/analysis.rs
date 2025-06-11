use egg::{Analysis, DidMerge, EGraph, Id, Language, Pattern};
use itertools::{Itertools, chain};
use rustc_hash::FxHashSet;
use utils::ereturn_if;

pub trait IntersectionHelper {
    fn convered_by_frame(&self, id: Id) -> bool;
}

/// A region of a random tape
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Region {
    /// The nonces
    nonces: FxHashSet<Id>,
    /// Whether this region covers the region of the previous frame
    frame: Vec<Id>,
}

impl Region {
    pub fn nonces(&self) -> &FxHashSet<Id> {
        &self.nonces
    }

    pub fn frame(&self) -> &[Id] {
        self.frame.as_ref()
    }

    pub fn has_frame(&self) -> bool {
        !self.frame().is_empty()
    }

    /// Builds the intersection of the two honnest random tape region
    ///
    /// If to build a term one *may* need to region `self` **and** one may need
    /// to region `other`. Then we know that we only need the intersection of
    /// those two regions. The difficulty appears when merging inputs and regular
    /// nonces.
    ///
    /// For instance, let's say step `A` uses nonces `n` and so does `B`. Then
    /// what should the intersection of `n` and `input(A)` be? It is `n` if `B`
    /// is before `A` and `empty` otherwise...
    ///
    /// For the current implementation we overapproximate and assumme the intesection
    /// is `n` in all cases.
    ///
    /// The `IntesectionHelper` is used to get access to the egraph to decide if a nonce
    /// exists the protocol; therefore if it colides with an input
    pub fn intersection(&self, other: &Self, helper: &impl IntersectionHelper) -> Self {
        ereturn_if!(self == other, self.clone()); // short path for equlality
        let iter = self.nonces().intersection(other.nonces()).copied();
        let frame = chain!(self.frame(), other.frame())
            .copied()
            .unique()
            .collect();
        if self.has_frame() || other.has_frame() {
            let nonces = chain!(
                iter,
                self.nonces()
                    .iter()
                    .filter(|&&id| helper.convered_by_frame(id))
                    .copied()
            )
            .collect();
            Self { nonces, frame }
        } else {
            let nonces = iter.collect();
            Self { nonces, frame }
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        ereturn_if!(self == other, self.clone());
        Self {
            nonces: self.nonces().union(other.nonces()).copied().collect(),
            frame: chain!(self.frame(), other.frame())
                .copied()
                .unique()
                .collect(),
        }
    }
}

mod iterator {
    use super::{IntersectionHelper, Region};

    pub trait Intersectable<U> {
        type Item;
        fn intersection(&mut self, with: U) -> Option<Self::Item>;
    }

    pub trait Unionable<U> {
        type Item;
        fn union(&mut self, with: U) -> Option<Self::Item>;
    }

    impl<'a, 'b, I, H> Intersectable<&'a H> for I
    where
        I: Iterator<Item = &'b Region>,
        H: IntersectionHelper,
    {
        type Item = Region;

        fn intersection(&mut self, helper: &'a H) -> Option<Self::Item> {
            let init = self.next()?;
            let init = init.intersection(self.next().unwrap_or(init), helper);
            Some(self.fold(init, |acc, e| acc.intersection(e, helper)))
        }
    }

    impl<'b, I> Unionable<()> for I
    where
        I: Iterator<Item = &'b Region>,
    {
        type Item = Region;

        fn union(&mut self, with: ()) -> Option<Self::Item> {
            let init = self.next()?;
            let init = init.union(self.next().unwrap_or(init));
            Some(self.fold(init, |acc, e| acc.union(e)))
        }
    }
}
pub use iterator::{Intersectable, Unionable};

impl IntersectionHelper for FxHashSet<Id> {
    fn convered_by_frame(&self, id: Id) -> bool {
        self.contains(&id)
    }
}
