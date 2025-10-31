use std::iter::Sum;
use std::ops::Add;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Default)]
pub struct SuperTuple<U, V>(pub U, pub V);

impl<U, V> Add<Self> for SuperTuple<U, V>
where
    U: Add<U, Output = U>,
    V: Add<V, Output = V>,
{
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
    fn sum<I: Iterator<Item = Self>>(mut iter: I) -> Self {
        let mut sum = iter.next().unwrap_or_default();
        for x in iter {
            sum = sum + x;
        }
        sum
    }
}

impl<U, V> From<(U, V)> for SuperTuple<U, V> {
    fn from((a, b): (U, V)) -> Self {
        Self(a, b)
    }
}

pub type MWeight = SuperTuple<u32, u32>;

pub trait Weight {
    fn decreases(&self, other: &Self) -> bool;
    fn min() -> Self;
}

impl Weight for () {
    fn decreases(&self, _: &Self) -> bool {
        true
    }

    fn min() -> Self {}
}

impl Weight for MWeight {
    fn decreases(&self, other: &Self) -> bool {
        self < other
    }

    fn min() -> Self {
        (0, 1).into()
    }
}
