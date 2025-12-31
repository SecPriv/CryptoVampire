//! Slice-like object for references
//!
//! See [VecRef]
use std::borrow::Cow;
use std::iter::FusedIterator;
use std::ops::Index;
use std::slice::Iter;
use std::sync::Arc;

use super::arc_into_iter::ArcIntoIter;
use crate::match_as_trait;

/// Slice-like object for references
///
/// To iterate over `&'s T`.
///
/// Most notably it accepts `Vec<&'a T>`, `&'a [T]`, `&'a [&'a T]`
/// single `&'a T` and the empty iterator.
///
/// Note that it is cheap to clone (ie. almost free)
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub enum VecRef<'a, T> {
    Vec(Arc<[&'a T]>),
    Ref(&'a [T]),
    RefRef(&'a [&'a T]),
    Single(&'a T),
    #[default]
    Empty,
}

impl<'a, T> VecRef<'a, T> {
    pub fn len(&self) -> usize {
        match self {
            VecRef::Vec(v) => v.len(),
            VecRef::Ref(v) => v.len(),
            VecRef::RefRef(v) => v.len(),
            VecRef::Single(_) => 0,
            VecRef::Empty => 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, i: usize) -> Option<&T> {
        match self {
            VecRef::Vec(v) => v.get(i).copied(),
            VecRef::Ref(v) => v.get(i),
            VecRef::RefRef(v) => v.get(i).copied(),
            VecRef::Single(e) => (i == 0).then_some(*e),
            VecRef::Empty => None,
        }
    }

    pub fn iter(&'_ self) -> IterVecRef<'a, '_, T> {
        self.into_iter()
    }
}

impl<'a, T> Index<usize> for VecRef<'a, T> {
    type Output = T;

    fn index(&self, i: usize) -> &Self::Output {
        match self {
            VecRef::Vec(v) => v[i],
            VecRef::Ref(v) => &v[i],
            VecRef::RefRef(v) => v[i],
            VecRef::Single(e) => {
                assert_eq!(i, 0);
                e
            }
            VecRef::Empty => panic!(),
        }
    }
}

impl<'a, 'b, T> IntoIterator for &'b VecRef<'a, T> {
    type Item = &'a T;

    type IntoIter = IterVecRef<'a, 'b, T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            VecRef::Vec(v) => IterVecRef::Ref(v.iter()),
            VecRef::Ref(v) => IterVecRef::Vec(v.iter()),
            VecRef::RefRef(v) => IterVecRef::Ref(v.iter()),
            VecRef::Single(e) => IterVecRef::Single(*e),
            VecRef::Empty => IterVecRef::Empty,
        }
    }
}

impl<'a, T> IntoIterator for VecRef<'a, T> {
    type Item = &'a T;

    type IntoIter = IterVecRef<'a, 'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            VecRef::Vec(v) => IterVecRef::OwnedVec(v.into()),
            VecRef::Ref(v) => IterVecRef::Vec(v.iter()),
            VecRef::RefRef(v) => IterVecRef::Ref(v.iter()),
            VecRef::Single(e) => IterVecRef::Single(e),
            VecRef::Empty => IterVecRef::Empty,
        }
    }
}

#[derive(Debug, Clone)]
pub enum IterVecRef<'a, 'b, T> {
    OwnedVec(ArcIntoIter<&'a T>),
    Vec(Iter<'a, T>),
    Ref(Iter<'b, &'a T>),
    Single(&'a T),
    Empty,
}

impl<'a, 'b, T> Iterator for IterVecRef<'a, 'b, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IterVecRef::OwnedVec(iter) => iter.next(),
            IterVecRef::Vec(iter) => iter.next(),
            IterVecRef::Ref(iter) => iter.next().copied(),
            IterVecRef::Single(e) => {
                let r = Some(*e);
                *self = IterVecRef::Empty;
                r
            }
            IterVecRef::Empty => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            IterVecRef::OwnedVec(iter) => iter.size_hint(),
            IterVecRef::Vec(iter) => iter.size_hint(),
            IterVecRef::Ref(iter) => iter.size_hint(),
            IterVecRef::Single(_) => (1, Some(1)),
            IterVecRef::Empty => (0, Some(0)),
        }
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        match self {
            Self::OwnedVec(v) => B::from_iter(v),
            Self::Vec(v) => B::from_iter(v),
            Self::Ref(v) => B::from_iter(v.cloned()),
            Self::Single(v) => Some(v).into_iter().collect(),
            Self::Empty => None.into_iter().collect(),
        }
    }
}

impl<'a, 'b, T> FusedIterator for IterVecRef<'a, 'b, T> {}

impl<'a, 'b, T> ExactSizeIterator for IterVecRef<'a, 'b, T> {}

impl<'a, 'b, T> DoubleEndedIterator for IterVecRef<'a, 'b, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            IterVecRef::OwnedVec(iter) => iter.next_back(),
            IterVecRef::Vec(iter) => iter.next_back(),
            IterVecRef::Ref(iter) => iter.next_back().copied(),
            IterVecRef::Single(_) => self.next(),
            IterVecRef::Empty => None,
        }
    }
}

impl<'a, I> FromIterator<&'a I> for VecRef<'a, I> {
    fn from_iter<T: IntoIterator<Item = &'a I>>(iter: T) -> Self {
        Self::Vec(FromIterator::from_iter(iter))
    }
}

impl<'a, T> From<&'a [T]> for VecRef<'a, T> {
    fn from(value: &'a [T]) -> Self {
        Self::Ref(value)
    }
}

impl<'a, T> From<&'a Arc<[T]>> for VecRef<'a, T> {
    fn from(value: &'a Arc<[T]>) -> Self {
        Self::Ref(value.as_ref())
    }
}

impl<'a, T, const N: usize> From<&'a [T; N]> for VecRef<'a, T> {
    fn from(value: &'a [T; N]) -> Self {
        Self::Ref(value.as_slice())
    }
}

impl<'a, T> From<&'a [&'a T]> for VecRef<'a, T> {
    fn from(value: &'a [&'a T]) -> Self {
        Self::RefRef(value)
    }
}

impl<'a, T> From<Vec<&'a T>> for VecRef<'a, T> {
    fn from(value: Vec<&'a T>) -> Self {
        Self::Vec(value.into_boxed_slice().into())
    }
}

impl<'a, T, const N: usize> From<[&'a T; N]> for VecRef<'a, T> {
    fn from(value: [&'a T; N]) -> Self {
        Self::Vec(Arc::new(value))
    }
}

impl<'a, T> From<&'a Box<[T]>> for VecRef<'a, T> {
    fn from(value: &'a Box<[T]>) -> Self {
        Self::Ref(value)
    }
}

impl<'a, U> Extend<&'a U> for VecRef<'a, U> {
    fn extend<T: IntoIterator<Item = &'a U>>(&mut self, iter: T) {
        let new = Self::Vec(self.iter().chain(iter).collect());
        *self = new;
    }
}

impl<'a, U> From<Cow<'a, [U]>> for VecRef<'a, U>
where
    [U]: ToOwned,
{
    fn from(value: Cow<'a, [U]>) -> Self {
        match value {
            Cow::Borrowed(_) => todo!(),
            Cow::Owned(_) => todo!(),
        }
    }
}

/// a [VecRef] with one more case when it needs to own the content
///
/// `T` must then be [Clone] because the owned [Iterator] cannot return
/// meaningful references, hence it clones the elements. Thus cloning
/// should be very cheap (intuitively `T` should be [Copy])
///
/// Note that [VecRefClone] is itself very cheap to clone
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum VecRefClone<'a, T>
where
    T: Clone,
{
    VecRef(VecRef<'a, T>),
    Vec(Arc<[T]>),
    Owned(T),
}

impl<'a, T: Clone> VecRefClone<'a, T> {
    pub fn len(&self) -> usize {
        match_as_trait!(self => {Self::VecRef(x) | Self::Vec(x) => {x.len()}, _ => {1}})
    }

    pub fn is_empty(&self) -> bool {
        match_as_trait!(self => {Self::VecRef(x) | Self::Vec(x) => {x.is_empty()}, _ => {false}})
    }

    pub fn get(&self, i: usize) -> Option<&T> {
        match self {
            Self::VecRef(x) => x.get(i),
            Self::Vec(x) => x.get(i),
            Self::Owned(x) if i == 0 => Some(x),
            _ => None,
        }
    }

    pub fn iter(&'a self) -> IterVecRef<'a, 'a, T> {
        IntoIterator::into_iter(self)
    }
}

impl<'a, T: Clone> Default for VecRefClone<'a, T> {
    fn default() -> Self {
        Self::VecRef(Default::default())
    }
}

impl<'a, T: Clone> Index<usize> for VecRefClone<'a, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<'b, 'a: 'b, T: Clone> IntoIterator for &'b VecRefClone<'a, T> {
    type Item = &'b T;

    type IntoIter = IterVecRef<'b, 'b, T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            VecRefClone::VecRef(x) => x.into_iter(),
            VecRefClone::Vec(x) => VecRef::from(x).into_iter(),
            VecRefClone::Owned(x) => VecRef::Single(x).into_iter(),
        }
    }
}

impl<'a, T: Clone> IntoIterator for VecRefClone<'a, T> {
    type Item = T;

    type IntoIter = IntoIterVecRefClone<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            VecRefClone::VecRef(x) => IntoIterVecRefClone::VecRef(x.into_iter()),
            VecRefClone::Vec(x) => IntoIterVecRefClone::Vec(x.into()),
            VecRefClone::Owned(x) => IntoIterVecRefClone::One(x),
        }
    }
}

#[derive(Debug, Clone)]
pub enum IntoIterVecRefClone<'a, T>
where
    T: Clone,
{
    VecRef(IterVecRef<'a, 'a, T>),
    Vec(ArcIntoIter<T>),
    One(T),
}

#[derive(Debug, Clone)]
pub enum IterVecRefClone<'a, 'b, T>
where
    T: Clone,
{
    VecRef(IterVecRef<'a, 'b, T>),
    Vec(Iter<'b, T>),
}

impl<'a, T> Iterator for IntoIterVecRefClone<'a, T>
where
    T: Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::VecRef(x) => x.next().cloned(),
            Self::Vec(x) => x.next(),
            Self::One(_) => {
                if let Self::One(x) = std::mem::replace(self, Self::VecRef(IterVecRef::Empty)) {
                    Some(x)
                } else {
                    unreachable!()
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::VecRef(x) => x.size_hint(),
            Self::Vec(x) => x.size_hint(),
            _ => (1, Some(1)),
        }
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        match self {
            Self::VecRef(x) => B::from_iter(x.cloned()),
            Self::Vec(x) => B::from_iter(x),
            Self::One(x) => B::from_iter([x]),
        }
    }
}

impl<'a, T: Clone> FusedIterator for IntoIterVecRefClone<'a, T> {}

impl<'a, T: Clone> ExactSizeIterator for IntoIterVecRefClone<'a, T> {}

impl<'a, T: Clone> DoubleEndedIterator for IntoIterVecRefClone<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::VecRef(x) => x.next_back().cloned(),
            Self::Vec(x) => x.next_back(),
            Self::One(_) => self.next(),
        }
    }
}

impl<'a, 'b, T> Iterator for IterVecRefClone<'a, 'b, T>
where
    T: Clone,
    'a: 'b,
{
    type Item = &'b T;

    fn next(&mut self) -> Option<Self::Item> {
        match_as_trait!(self => {Self::VecRef(x) | Self::Vec(x) => {x.next()}})
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match_as_trait!(self => {Self::VecRef(x) | Self::Vec(x) => {x.size_hint()}})
    }
}

impl<'b, 'a: 'b, T: Clone> FusedIterator for IterVecRefClone<'a, 'b, T> {}

impl<'b, 'a: 'b, T: Clone> ExactSizeIterator for IterVecRefClone<'a, 'b, T> {}

impl<'b, 'a: 'b, T: Clone> DoubleEndedIterator for IterVecRefClone<'a, 'b, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match_as_trait!(self => {Self::VecRef(x) | Self::Vec(x) => {x.next_back()}})
    }
}

impl<'a, I> FromIterator<&'a I> for VecRefClone<'a, I>
where
    I: Clone,
{
    fn from_iter<T: IntoIterator<Item = &'a I>>(iter: T) -> Self {
        Self::VecRef(VecRef::from_iter(iter))
    }
}

impl<'a, I> FromIterator<I> for VecRefClone<'a, I>
where
    I: Clone,
{
    fn from_iter<T: IntoIterator<Item = I>>(iter: T) -> Self {
        Self::Vec(FromIterator::from_iter(iter))
    }
}

impl<'a, T> From<&'a [T]> for VecRefClone<'a, T>
where
    T: Clone,
{
    fn from(value: &'a [T]) -> Self {
        Self::VecRef(value.into())
    }
}

impl<'a, T, const N: usize> From<&'a [T; N]> for VecRefClone<'a, T>
where
    T: Clone,
{
    fn from(value: &'a [T; N]) -> Self {
        Self::VecRef(value.into())
    }
}

impl<'a, T, const N: usize> From<[T; N]> for VecRefClone<'a, T>
where
    T: Clone,
{
    fn from(value: [T; N]) -> Self {
        Self::Vec(Arc::new(value))
    }
}

impl<'a, T> From<&'a [&'a T]> for VecRefClone<'a, T>
where
    T: Clone,
{
    fn from(value: &'a [&'a T]) -> Self {
        Self::VecRef(value.into())
    }
}

impl<'a, T> From<Vec<&'a T>> for VecRefClone<'a, T>
where
    T: Clone,
{
    fn from(value: Vec<&'a T>) -> Self {
        Self::VecRef(value.into())
    }
}

impl<'a, T> From<Vec<T>> for VecRefClone<'a, T>
where
    T: Clone,
{
    fn from(value: Vec<T>) -> Self {
        Self::Vec(value.into_boxed_slice().into())
    }
}

impl<'a, T> From<Box<[T]>> for VecRefClone<'a, T>
where
    T: Clone,
{
    fn from(value: Box<[T]>) -> Self {
        Self::Vec(value.into())
    }
}
impl<'a, T> From<&'a Box<[T]>> for VecRefClone<'a, T>
where
    T: Clone,
{
    fn from(value: &'a Box<[T]>) -> Self {
        Self::VecRef(value.into())
    }
}

impl<'a, T: Clone> From<Arc<[T]>> for VecRefClone<'a, T> {
    fn from(value: Arc<[T]>) -> Self {
        Self::Vec(value)
    }
}

impl<'a, 'b, T: Clone> From<&'b Arc<[T]>> for VecRefClone<'a, T> {
    fn from(value: &'b Arc<[T]>) -> Self {
        Self::Vec(Arc::clone(value))
    }
}

impl<'a, U: Clone> Extend<U> for VecRefClone<'a, U> {
    /// This is *very* expensive for this type
    fn extend<T: IntoIterator<Item = U>>(&mut self, iter: T) {
        let new = Self::Vec(self.clone().into_iter().chain(iter).collect());
        *self = new;
    }
}

#[cfg(test)]
mod tests {
    use crate::vecref::{VecRef, VecRefClone};

    #[test]
    fn they_are_small() {
        assert_eq!(
            std::mem::size_of::<VecRef<'static, usize>>(),
            std::mem::size_of::<VecRefClone<'static, usize>>()
        )
    }
}
