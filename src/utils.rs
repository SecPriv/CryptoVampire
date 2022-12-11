use std::{slice::Iter, sync::Arc};

#[derive(Debug, Eq, Hash, Default)]
pub struct RcEq<S>(pub Arc<S>);

impl<S: PartialEq> PartialEq for RcEq<S> {
    fn eq(&self, other: &Self) -> bool {
        Arc::as_ptr(&self.0) == Arc::as_ptr(&other.0)
    }
}
impl<S: PartialOrd> PartialOrd for RcEq<S> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.0.partial_cmp(&other.0) {
            Some(std::cmp::Ordering::Equal) => {
                Arc::as_ptr(&self.0).partial_cmp(&Arc::as_ptr(&other.0))
            }
            o => o,
        }
    }
}
impl<S: Ord> Ord for RcEq<S> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.cmp(&other.0) {
            std::cmp::Ordering::Equal => Arc::as_ptr(&self.0).cmp(&Arc::as_ptr(&other.0)),
            o => o,
        }
    }
}
impl<S> Clone for RcEq<S> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<S> RcEq<S> {
    pub fn new(s: S) -> Self {
        RcEq(Arc::new(s))
    }
}

pub struct IntersectionVecIterator<'a, T> {
    a: &'a [T],
    b: Iter<'a, T>,
}

impl<'a, T> IntersectionVecIterator<'a, T> {
    pub fn new(a: &'a [T], b: &'a [T]) -> Self {
        let (a, b) = ord_utils::sort_by(|&a, &b| a.len() <= b.len(), a, b);
        IntersectionVecIterator { a, b: b.iter() }
    }
}

impl<'a, T> Iterator for IntersectionVecIterator<'a, T>
where
    T: Eq,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.b.next()?;
        if self.a.contains(n) {
            Some(n)
        } else {
            self.next()
        }
    }
}
