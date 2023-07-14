//! Slice-like object for references
//!
//! See [VecRef]
use std::{iter::FusedIterator, ops::Index, slice::Iter, vec::IntoIter};

/// Slice-like object for references
///
/// To iterate over `&'s T`.
///
/// Most notably it accepts `Vec<&'a T>`, `&'a [T]`, `&'a [&'a T]`
/// single `&'a T` and the empty iterator.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum VecRef<'a, T> {
    Vec(Vec<&'a T>),
    Ref(&'a [T]),
    RefRef(&'a [&'a T]),
    Single(&'a T),
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

    pub fn get(&self, i: usize) -> Option<&T> {
        match self {
            VecRef::Vec(v) => v.get(i).map(|e| *e),
            VecRef::Ref(v) => v.get(i),
            VecRef::RefRef(v) => v.get(i).map(|e| *e),
            VecRef::Single(e) => (i == 0).then(|| *e),
            VecRef::Empty => None,
        }
    }

    pub unsafe fn get_unchecked(&self, i: usize) -> &'a T {
        match self {
            VecRef::Vec(v) => v.get_unchecked(i),
            VecRef::Ref(v) => v.get_unchecked(i),
            VecRef::RefRef(v) => v.get_unchecked(i),
            VecRef::Single(e) => {
                assert_eq!(0, i);
                *e
            }
            VecRef::Empty => panic!(),
        }
    }

    pub fn iter(&'_ self) -> impl Iterator<Item = &'a T> + '_ {
        self.into_iter()
    }
}

impl<'a, T> Index<usize> for VecRef<'a, T> {
    type Output = T;

    fn index(&self, i: usize) -> &Self::Output {
        match self {
            VecRef::Vec(v) => &v[i],
            VecRef::Ref(v) => &v[i],
            VecRef::RefRef(v) => v[i],
            VecRef::Single(e) => {
                assert_eq!(i, 0);
                *e
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
            VecRef::Vec(v) => IterVecRef::OwnedVec(v.into_iter()),
            VecRef::Ref(v) => IterVecRef::Vec(v.iter()),
            VecRef::RefRef(v) => IterVecRef::Ref(v.iter()),
            VecRef::Single(e) => IterVecRef::Single(e),
            VecRef::Empty => IterVecRef::Empty,
        }
    }
}

#[derive(Debug, Clone)]
pub enum IterVecRef<'a, 'b, T> {
    OwnedVec(IntoIter<&'a T>),
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
            IterVecRef::Ref(iter) => iter.next().map(|e| *e),
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
}

impl<'a, 'b, T> FusedIterator for IterVecRef<'a, 'b, T> {}

impl<'a, 'b, T> ExactSizeIterator for IterVecRef<'a, 'b, T> {}

impl<'a, 'b, T> DoubleEndedIterator for IterVecRef<'a, 'b, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            IterVecRef::OwnedVec(iter) => iter.next_back(),
            IterVecRef::Vec(iter) => iter.next_back(),
            IterVecRef::Ref(iter) => iter.next_back().map(|e| *e),
            IterVecRef::Single(_) => self.next(),
            IterVecRef::Empty => None,
        }
    }
}
