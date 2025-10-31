use std::iter::FusedIterator;
use std::sync::Arc;

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum ArcIntoIter<T> {
    Empty,
    Iter {
        data: Arc<[T]>,
        index: usize,
        end: usize,
    },
}

impl<T> ArcIntoIter<T> {
    pub fn empty() -> Self {
        Self::default()
    }
}

impl<T: Clone> Iterator for ArcIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ArcIntoIter::Empty => None,
            ArcIntoIter::Iter { data, index, end } => {
                if index != end {
                    let e = data.get(*index).unwrap();
                    *index += 1;
                    Some(e.clone())
                } else {
                    *self = Self::Empty;
                    self.next()
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            ArcIntoIter::Empty => (0, Some(0)),
            ArcIntoIter::Iter {
                data: _,
                index,
                end,
            } => {
                let len = *end - *index;
                (len, Some(len))
            }
        }
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        match self {
            ArcIntoIter::Empty => B::from_iter(std::iter::empty()),
            ArcIntoIter::Iter { data, index, end } => {
                B::from_iter(data.as_ref()[index..end].iter().cloned())
            }
        }
    }
}

impl<T: Clone> FusedIterator for ArcIntoIter<T> {}

impl<T: Clone> ExactSizeIterator for ArcIntoIter<T> {}

impl<T: Clone> DoubleEndedIterator for ArcIntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            ArcIntoIter::Empty => None,
            ArcIntoIter::Iter { data, index, end } => {
                if index != end {
                    *end -= 1;
                    let e = data.get(*end).unwrap();
                    Some(e.clone())
                } else {
                    *self = Self::Empty;
                    self.next()
                }
            }
        }
    }
}

impl<T> From<Arc<[T]>> for ArcIntoIter<T> {
    fn from(value: Arc<[T]>) -> Self {
        ArcIntoIter::Iter {
            end: value.len(),
            data: value,
            index: 0,
        }
    }
}

impl<'a, T> From<&'a Arc<[T]>> for ArcIntoIter<T> {
    fn from(value: &'a Arc<[T]>) -> Self {
        if value.is_empty() {
            Self::Empty
        } else {
            ArcIntoIter::Iter {
                end: value.len(),
                data: Arc::clone(value),
                index: 0,
            }
        }
    }
}

impl<T, const N: usize> From<[T; N]> for ArcIntoIter<T> {
    fn from(value: [T; N]) -> Self {
        if N == 0 {
            Self::Empty
        } else {
            Self::Iter {
                data: Arc::new(value),
                index: 0,
                end: N,
            }
        }
    }
}

impl<T> Default for ArcIntoIter<T> {
    fn default() -> Self {
        [].into()
    }
}

pub trait ClonableArc<T>: Sized
where
    T: Clone,
{
    fn clonnable_arc(self) -> Arc<[T]>;
    fn into_iter(self) -> ArcIntoIter<T> {
        ArcIntoIter::from(self.clonnable_arc())
    }
}

impl<T: Clone> ClonableArc<T> for Arc<[T]> {
    fn clonnable_arc(self) -> Arc<[T]> {
        self
    }
}

impl<T> FromIterator<T> for ArcIntoIter<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let data: Arc<[_]> = iter.into_iter().collect();
        data.into()
    }
}
