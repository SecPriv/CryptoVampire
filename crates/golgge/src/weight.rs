use std::iter::Sum;
use std::ops::Add;

/// A generic tuple struct used for combining two comparable values, typically for weighting.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Default)]
pub struct SuperTuple<U, V>(
    /// The first component of the tuple.
    pub U,
    /// The second component of the tuple.
    pub V,
);

impl<U, V> Add<Self> for SuperTuple<U, V>
where
    U: Add<U, Output = U>,
    V: Add<V, Output = V>,
{
    /// Adds two `SuperTuple` instances element-wise.
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let Self(a1, b1) = self;
        let Self(a2, b2) = rhs;
        Self(a1 + a2, b1 + b2)
    }
}

impl<U, V> Sum<Self> for SuperTuple<U, V>
where
    U: Add<U, Output = U> + Default,
    V: Add<V, Output = V> + Default,
{
    /// Sums an iterator of `SuperTuple` instances element-wise.
    fn sum<I: Iterator<Item = Self>>(mut iter: I) -> Self {
        let mut sum = iter.next().unwrap_or_default();
        for x in iter {
            sum = sum + x;
        }
        sum
    }
}

impl<U, V> From<(U, V)> for SuperTuple<U, V> {
    /// Converts a tuple `(U, V)` into a `SuperTuple<U, V>`.
    fn from((a, b): (U, V)) -> Self {
        Self(a, b)
    }
}

/// A type alias for `SuperTuple<u32, u32>`, representing a weight with two components.
pub type MWeight = SuperTuple<u32, u32>;

/// A trait for types that can represent a weight and compare for decrease.
pub trait Weight {
    /// Returns `true` if `self` decreases `other`.
    fn decreases(&self, other: &Self) -> bool;
    /// Returns the minimum possible weight.
    fn min() -> Self;
}

impl Weight for () {
    /// Always returns `true` as the unit type has no meaningful weight comparison.
    fn decreases(&self, _: &Self) -> bool {
        true
    }

    /// Returns the unit value.
    fn min() -> Self {}
}

impl Weight for MWeight {
    /// Returns `true` if `self` is less than `other`.
    fn decreases(&self, other: &Self) -> bool {
        self < other
    }

    /// Returns the minimum `MWeight`.
    fn min() -> Self {
        (0, 1).into()
    }
}
