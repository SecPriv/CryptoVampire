use egg::{Analysis, DidMerge, EGraph, Id, Language, Pattern};
use itertools::{chain, Itertools};
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
    frame: bool,
}

impl Region {
    pub fn nonces(&self) -> &FxHashSet<Id> {
        &self.nonces
    }

    pub fn frame(&self) -> bool {
        self.frame
    }

    pub fn intersection(&self, other: &Self, helper: &impl IntersectionHelper) -> Self {
        ereturn_if!(self == other, self.clone());
        let iter = self.nonces().intersection(other.nonces()).copied();
        if self.frame() || other.frame() {
            let nonces = chain!(
                iter,
                self.nonces()
                    .iter()
                    .filter(|&&id| helper.convered_by_frame(id))
                    .copied()
            )
            .collect();
            Self {
                nonces,
                frame: false,
            }
        } else {
            let nonces = iter.collect();
            Self {
                nonces,
                frame: self.frame() && other.frame(),
            }
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        ereturn_if!(self == other, self.clone());
        Self {
            nonces: self.nonces().union(other.nonces()).copied().collect(),
            frame: self.frame() || other.frame(),
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
        I: Iterator<Item = &'b Region>, {
            type Item = Region;
        
            fn union(&mut self, with: ()) -> Option<Self::Item> {
            let init = self.next()?;
            let init = init.intersection(self.next().unwrap_or(init), helper);
            Some(self.fold(init, |acc, e| acc.intersection(e, helper)))
        }
        }
        
}
pub use iterator::{Intersectable, Unionable};

impl IntersectionHelper for FxHashSet<Id> {
    fn convered_by_frame(&self, id: Id) -> bool {
        self.contains(&id)
    }
}
