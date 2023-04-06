use std::{ops::Index, slice::Iter};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum VecRef<'a, T> {
    Vec(Vec<&'a T>),
    Ref(&'a Vec<T>),
    RefRef(&'a Vec<&'a T>),
}

macro_rules! mmap {
    ($arr:expr, $v:ident, $b:block) => {
        match $arr {
            VecRef::Vec($v) => $b,
            VecRef::Ref($v) => $b,
            VecRef::RefRef($v) => $b,
        }
    };
}

impl<'a, T> VecRef<'a, T> {
    pub fn len(&self) -> usize {
        mmap!(self, v, { v.len() })
    }

    pub fn get(&self, i: usize) -> Option<&T> {
        match self {
            VecRef::Vec(v) => v.get(i).map(|e| *e),
            VecRef::Ref(v) => v.get(i),
            VecRef::RefRef(v) => v.get(i).map(|e| *e),
        }
    }

    pub unsafe fn get_unchecked(&self, i: usize) -> &'a T {
        mmap!(self, v, { v.get_unchecked(i) })
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
        }
    }
}

#[derive(Debug, Clone)]
pub enum IterVecRef<'a, T> {
    Vec(Iter<'a, T>),
    Ref(Iter<'a, &'a T>),
}

impl<'a, T> Iterator for IterVecRef<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IterVecRef::Vec(iter) => iter.next(),
            IterVecRef::Ref(iter) => iter.next().map(|e| *e),
        }
    }
}
