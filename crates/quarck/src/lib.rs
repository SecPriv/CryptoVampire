mod cowarc {
    use std::fmt::{Debug, Display};
    use std::hash::Hash;
    use std::iter::FusedIterator;
    use std::ops::{Deref, Index};
    use std::sync::Arc;

    // #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
    pub enum CowArc<'a, U: ?Sized> {
        Owned(Arc<U>),
        Borrowed(&'a U),
    }

    impl<U: ?Sized> Deref for CowArc<'_, U> {
        type Target = U;

        #[inline]
        fn deref(&self) -> &Self::Target {
            match self {
                CowArc::Owned(o) => o,
                CowArc::Borrowed(a) => a,
            }
        }
    }

    impl<U: ?Sized> Clone for CowArc<'_, U> {
        #[inline]
        fn clone(&self) -> Self {
            match self {
                Self::Owned(arg0) => Self::Owned(arg0.clone()),
                Self::Borrowed(arg0) => Self::Borrowed(arg0),
            }
        }
    }
    impl<U: ?Sized + Eq> Eq for CowArc<'_, U> {}
    impl<U: ?Sized + PartialEq> PartialEq for CowArc<'_, U> {
        fn eq(&self, other: &Self) -> bool {
            self.deref().eq(other)
        }
    }
    impl<U: ?Sized + Ord> Ord for CowArc<'_, U> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.deref().cmp(other)
        }
    }
    impl<U: ?Sized + PartialOrd> PartialOrd for CowArc<'_, U> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.deref().partial_cmp(other)
        }
    }
    impl<U: ?Sized + Hash> Hash for CowArc<'_, U> {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.deref().hash(state);
        }
    }
    impl<U: ?Sized + Display> Display for CowArc<'_, U> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.deref().fmt(f)
        }
    }
    impl<U: ?Sized + Debug> Debug for CowArc<'_, U> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.deref().fmt(f)
        }
    }

    impl<'a, U: Default> Default for CowArc<'a, U> {
        fn default() -> Self {
            Self::Owned(Arc::new(U::default()))
        }
    }

    impl<'a, U> Default for CowArc<'a, [U]> {
        fn default() -> Self {
            Self::Owned(vec![].into())
        }
    }

    impl<U> From<U> for CowArc<'_, U> {
        fn from(value: U) -> Self {
            Self::Owned(Arc::new(value))
        }
    }

    impl<U: ?Sized> AsRef<U> for CowArc<'_, U> {
        fn as_ref(&self) -> &U {
            match self {
                Self::Owned(x) => Arc::as_ref(x),
                Self::Borrowed(x) => x,
            }
        }
    }
    impl<'a, U> CowArc<'a, U> {
        pub fn new(x: U) -> Self {
            Self::Owned(Arc::new(x))
        }
    }

    impl<'a, U: ?Sized> CowArc<'a, U> {
        pub const fn from_ref(value: &'a U) -> Self {
            CowArc::Borrowed(value)
        }

        /// Prefer [Self::into_inner]
        #[deprecated = "prefer `into_innner`"]
        pub fn as_owned(&self) -> <U as ToOwned>::Owned
        where
            U: ToOwned,
        {
            self.deref().to_owned()
        }

        pub fn into_inner(self) -> U
        where
            U: Clone,
        {
            Arc::unwrap_or_clone(self.into_arc())
        }

        pub fn make_owned(&mut self)
        where
            U: Clone,
        {
            if let Self::Borrowed(x) = self {
                *self = Self::Owned(Arc::new(x.clone()))
            }
        }

        pub fn into_owned<'b>(self) -> CowArc<'b, U>
        where
            U: Clone,
        {
            match self {
                Self::Owned(x) => CowArc::Owned(x),
                Self::Borrowed(x) => CowArc::Owned(Arc::new(x.clone())),
            }
        }

        pub fn to_mut(&mut self) -> &mut U
        where
            U: Clone,
        {
            self.make_owned();
            let Self::Owned(arc) = self else {
                unreachable!()
            };
            Arc::make_mut(arc)
        }

        pub fn into_arc(mut self) -> Arc<U>
        where
            U: Clone,
        {
            self.make_owned();
            let Self::Owned(arc) = self else {
                unreachable!()
            };
            arc
        }
    }

    impl<'a, U> CowArc<'a, [U]>
    where
        U: Clone,
    {
        pub fn make_vec_owned(&mut self) {
            if let Self::Borrowed(x) = self {
                *self = x.iter().cloned().collect()
            }
        }

        pub fn to_mut_slice(&mut self) -> &mut [U] {
            self.make_vec_owned();
            let Self::Owned(arc) = self else {
                unreachable!()
            };
            Arc::make_mut(arc)
        }

        pub fn from_vec(vec: Vec<U>) -> Self {
            Self::Owned(vec.into())
        }

        #[allow(private_interfaces)]
        pub fn into_cloned_iter(&self) -> CowArcOwnedIter<'a, U> {
            CowArcOwnedIter {
                arr: self.clone(),
                start: 0,
                end: self.len(),
            }
        }

        pub fn into_vec_arc(mut self) -> Arc<[U]> {
            self.make_vec_owned();
            let Self::Owned(arc) = self else {
                unreachable!()
            };
            arc
        }

        pub fn into_vec_owned<'b>(self) -> CowArc<'b, [U]>
        where
            U: Clone,
        {
            match self {
                Self::Owned(x) => CowArc::Owned(x),
                Self::Borrowed(x) => CowArc::Owned(x.iter().cloned().collect()),
            }
        }
    }

    impl<'a, U, const N: usize> CowArc<'a, [U; N]> {
        pub fn forget_size(self) -> CowArc<'a, [U]> {
            match self {
                CowArc::Borrowed(x) => CowArc::Borrowed(x),
                CowArc::Owned(x) => CowArc::Owned(x),
            }
        }
    }

    #[cfg(feature = "serde")]
    impl<U: serde::Serialize + ?Sized> serde::Serialize for CowArc<'_, U> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            self.deref().serialize(serializer)
        }
    }
    #[cfg(feature = "serde")]
    impl<'de, U: serde::Deserialize<'de>> serde::Deserialize<'de> for CowArc<'_, U> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            Ok(U::deserialize(deserializer)?.into())
        }
    }

    impl<'a, T> FromIterator<T> for CowArc<'a, [T]> {
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            Self::Owned(iter.into_iter().collect())
        }
    }

    impl<'a, T> From<Vec<T>> for CowArc<'a, [T]> {
        fn from(value: Vec<T>) -> Self {
            Self::Owned(value.into())
        }
    }

    impl<'a, 'b, T> IntoIterator for &'b CowArc<'a, [T]> {
        type Item = &'b T;

        type IntoIter = ::std::slice::Iter<'b, T>;

        fn into_iter(self) -> Self::IntoIter {
            (*self).deref().iter()
        }
    }

    #[derive(Debug, Clone)]
    pub struct CowArcOwnedIter<'a, U> {
        arr: CowArc<'a, [U]>,
        start: usize,
        end: usize,
    }

    impl<'a, U: Clone> Iterator for CowArcOwnedIter<'a, U> {
        type Item = U;

        fn next(&mut self) -> Option<Self::Item> {
            let Self { arr, start, end } = self;
            if start < end {
                let i = *start;
                *start += 1;
                Some(arr[i].clone())
            } else {
                None
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let Self { start, end, .. } = self;
            let n = *start - *end;
            (n, Some(n))
        }
    }

    impl<'a, U: Clone> DoubleEndedIterator for CowArcOwnedIter<'a, U> {
        fn next_back(&mut self) -> Option<Self::Item> {
            let Self { arr, start, end } = self;
            if start < end {
                *end -= 1;
                Some(arr[*end].clone())
            } else {
                None
            }
        }
    }

    impl<'a, U: Clone> FusedIterator for CowArcOwnedIter<'a, U> {}

    impl<'a, U, const N: usize> From<[U; N]> for CowArc<'a, [U]> {
        fn from(value: [U; N]) -> Self {
            Self::Owned(Arc::new(value))
        }
    }
}
pub use cowarc::{CowArc, CowArcOwnedIter};

mod cowrc {
    use std::fmt::{Debug, Display};
    use std::hash::Hash;
    use std::ops::Deref;
    use std::rc::Rc;
    pub enum CowRc<'a, U: ?Sized> {
        Owned(Rc<U>),
        Borrowed(&'a U),
    }
    impl<U: ?Sized> Deref for CowRc<'_, U> {
        type Target = U;

        fn deref(&self) -> &Self::Target {
            match self {
                CowRc::Owned(o) => o,
                CowRc::Borrowed(a) => a,
            }
        }
    }

    impl<U: ?Sized> Clone for CowRc<'_, U> {
        fn clone(&self) -> Self {
            match self {
                Self::Owned(arg0) => Self::Owned(arg0.clone()),
                Self::Borrowed(arg0) => Self::Borrowed(arg0),
            }
        }
    }
    impl<U: ?Sized + Eq> Eq for CowRc<'_, U> {}
    impl<U: ?Sized + PartialEq> PartialEq for CowRc<'_, U> {
        fn eq(&self, other: &Self) -> bool {
            self.deref().eq(other)
        }
    }
    impl<U: ?Sized + Ord> Ord for CowRc<'_, U> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.deref().cmp(other)
        }
    }
    impl<U: ?Sized + PartialOrd> PartialOrd for CowRc<'_, U> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.deref().partial_cmp(other)
        }
    }
    impl<U: ?Sized + Hash> Hash for CowRc<'_, U> {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.deref().hash(state);
        }
    }
    impl<U: ?Sized + Display> Display for CowRc<'_, U> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.deref().fmt(f)
        }
    }
    impl<U: ?Sized + Debug> Debug for CowRc<'_, U> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.deref().fmt(f)
        }
    }

    impl<U> From<U> for CowRc<'_, U> {
        fn from(value: U) -> Self {
            Self::Owned(Rc::new(value))
        }
    }

    impl<'a, U: ?Sized> CowRc<'a, U> {
        pub const fn from_ref(value: &'a U) -> Self {
            CowRc::Borrowed(value)
        }

        pub fn as_owned(&self) -> <U as ToOwned>::Owned
        where
            U: ToOwned,
        {
            self.deref().to_owned()
        }
    }

    #[cfg(feature = "serde")]
    impl<U: serde::Serialize + ?Sized> serde::Serialize for CowRc<'_, U> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            self.deref().serialize(serializer)
        }
    }
    #[cfg(feature = "serde")]
    impl<'de, U: serde::Deserialize<'de>> serde::Deserialize<'de> for CowRc<'_, U> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            Ok(U::deserialize(deserializer)?.into())
        }
    }

    impl<'a, T> FromIterator<T> for CowRc<'a, [T]> {
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            Self::Owned(iter.into_iter().collect())
        }
    }

    impl<'a, T> From<Vec<T>> for CowRc<'a, [T]> {
        fn from(value: Vec<T>) -> Self {
            Self::Owned(value.into())
        }
    }

    impl<'a, U: Default> Default for CowRc<'a, U> {
        fn default() -> Self {
            Self::Owned(Rc::new(U::default()))
        }
    }

    impl<'a, U> Default for CowRc<'a, [U]> {
        fn default() -> Self {
            Self::Owned(vec![].into())
        }
    }
}
pub use cowrc::CowRc;
