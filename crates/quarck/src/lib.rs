mod cowarc {
    use std::fmt::{Debug, Display};
    use std::hash::Hash;
    use std::ops::Deref;
    use std::sync::Arc;

    // #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
    pub enum CowArc<'a, U: ?Sized> {
        Owned(Arc<U>),
        Borrowed(&'a U),
    }

    impl<U: ?Sized> Deref for CowArc<'_, U> {
        type Target = U;

        fn deref(&self) -> &Self::Target {
            match self {
                CowArc::Owned(o) => o,
                CowArc::Borrowed(a) => a,
            }
        }
    }

    impl<U: ?Sized> Clone for CowArc<'_, U> {
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

    impl<'a, U: ?Sized> CowArc<'a, U> {
        pub const fn from_ref(value: &'a U) -> Self {
            CowArc::Borrowed(value)
        }

        pub fn as_owned(&self) -> <U as ToOwned>::Owned
        where
            U: ToOwned,
        {
            self.deref().to_owned()
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
}
pub use cowarc::CowArc;

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
