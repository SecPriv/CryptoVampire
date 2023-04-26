use std::{iter::FusedIterator, ops::Index, slice::Iter, vec::IntoIter};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum VecRef<'a, T> {
    Vec(Vec<&'a T>),
    Ref(&'a [T]),
    RefRef(&'a [&'a T]),
    Empty,
}

// macro_rules! mmap {
//     ($arr:expr, $v:ident, $b:block) => {
//         match $arr {
//             VecRef::Vec($v) => $b,
//             VecRef::Ref($v) => $b,
//             VecRef::RefRef($v) => $b,
//         }
//     };
// }

impl<'a, T> VecRef<'a, T> {
    pub fn len(&self) -> usize {
        match self {
            VecRef::Vec(v) => v.len(),
            VecRef::Ref(v) => v.len(),
            VecRef::RefRef(v) => v.len(),
            VecRef::Empty => 0,
        }
    }

    pub fn get(&self, i: usize) -> Option<&T> {
        match self {
            VecRef::Vec(v) => v.get(i).map(|e| *e),
            VecRef::Ref(v) => v.get(i),
            VecRef::RefRef(v) => v.get(i).map(|e| *e),
            VecRef::Empty => None,
        }
    }

    pub unsafe fn get_unchecked(&self, i: usize) -> &'a T {
        match self {
            VecRef::Vec(v) => v.get_unchecked(i),
            VecRef::Ref(v) => v.get_unchecked(i),
            VecRef::RefRef(v) => v.get_unchecked(i),
            VecRef::Empty => panic!(),
        }
    }

    pub fn iter(&'a self) -> impl Iterator<Item = &'a T> {
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
            VecRef::Empty => panic!(),
        }
    }
}

impl<'a, T> IntoIterator for &'a VecRef<'a, T> {
    type Item = &'a T;

    type IntoIter = IterVecRef<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            VecRef::Vec(v) => IterVecRef::Ref(v.iter()),
            VecRef::Ref(v) => IterVecRef::Vec(v.iter()),
            VecRef::RefRef(v) => IterVecRef::Ref(v.iter()),
            VecRef::Empty => IterVecRef::Empty,
        }
    }
}

impl<'a, T> IntoIterator for VecRef<'a, T> {
    type Item = &'a T;

    type IntoIter = IterVecRef<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            VecRef::Vec(v) => IterVecRef::OwnedVec(v.into_iter()),
            VecRef::Ref(v) => IterVecRef::Vec(v.iter()),
            VecRef::RefRef(v) => IterVecRef::Ref(v.iter()),
            VecRef::Empty => IterVecRef::Empty,
        }
    }
}

#[derive(Debug, Clone)]
pub enum IterVecRef<'a, T> {
    OwnedVec(IntoIter<&'a T>),
    Vec(Iter<'a, T>),
    Ref(Iter<'a, &'a T>),
    Empty,
}

impl<'a, T> Iterator for IterVecRef<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IterVecRef::OwnedVec(iter) => iter.next(),
            IterVecRef::Vec(iter) => iter.next(),
            IterVecRef::Ref(iter) => iter.next().map(|e| *e),
            IterVecRef::Empty => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            IterVecRef::OwnedVec(iter) => iter.size_hint(),
            IterVecRef::Vec(iter) => iter.size_hint(),
            IterVecRef::Ref(iter) => iter.size_hint(),
            IterVecRef::Empty => (0, Some(0)),
        }
    }
}

impl<'a, T> FusedIterator for IterVecRef<'a, T> {}

impl<'a, T> ExactSizeIterator for IterVecRef<'a, T> {}

impl<'a, T> DoubleEndedIterator for IterVecRef<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            IterVecRef::OwnedVec(iter) => iter.next_back(),
            IterVecRef::Vec(iter) => iter.next_back(),
            IterVecRef::Ref(iter) => iter.next_back().map(|e| *e),
            IterVecRef::Empty => None,
        }
    }
}
