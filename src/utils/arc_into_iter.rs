use std::{iter::FusedIterator, sync::Arc};

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ArcIntoIter<T> {
    data: Arc<[T]>,
    index: usize,
    end: usize,
}

impl<T: Clone> Iterator for ArcIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index != self.end {
            let e = self.data.get(self.index).unwrap();
            self.index += 1;
            Some(e.clone())
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end - self.index;
        (len, Some(len))
    }
}

impl<T: Clone> FusedIterator for ArcIntoIter<T> {}

impl<T: Clone> ExactSizeIterator for ArcIntoIter<T> {}

impl<T: Clone> DoubleEndedIterator for ArcIntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index != self.end {
            self.end -= 1;
            let e = self.data.get(self.end).unwrap();
            Some(e.clone())
        } else {
            None
        }
    }
}

impl<T> From<Arc<[T]>> for ArcIntoIter<T> {
    fn from(value: Arc<[T]>) -> Self {
        ArcIntoIter {
            end: value.len(),
            data: value,
            index: 0,
        }
    }
}

impl<'a, T> From<&'a Arc<[T]>> for ArcIntoIter<T> {
    fn from(value: &'a Arc<[T]>) -> Self {
        ArcIntoIter {
            end: value.len(),
            data: Arc::clone(value),
            index: 0,
        }
    }
}
