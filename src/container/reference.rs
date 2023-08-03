use std::{
    cmp::Ordering, convert::Infallible, error::Error, fmt::Debug, hash::Hash, marker::PhantomData,
    ptr::NonNull,
};

use itertools::Itertools;

use crate::utils::{
    precise_as_ref::PreciseAsRef,
    utils::{AccessToInvalidData, AlreadyInitialized, MaybeInvalid},
};

use super::{
    allocator::{Container, ContainerTools},
    contained::{Contained, Containable},
};

// pub type RefPointee<'bump, R> = Option<<R as Reference<'bump>>::Inner>;
// pub type RefInner<'bump, R> = <R as Reference<'bump>>::Inner;

#[derive(PartialEq, Eq)]
pub struct Reference<'bump, T>  {
    inner: NonNull<Option<T>>,
    lt: PhantomData<&'bump ()>,
}

impl<'bump, T> Reference<'bump, T> {
    pub fn as_option_ref(&self) -> &'bump Option<T> {
        unsafe { self.inner.as_ref() }
    }

    pub fn as_inner(&self) -> &T {
        self.as_ref()
    }

    pub fn maybe_precise_as_ref(&self) -> Option<&'bump T> {
        self.as_option_ref().as_ref()
    }

    pub fn from_ref(ptr: &'bump Option<T>) -> Self {
        Self::from(ptr)
    }
}

impl<'bump, T> PreciseAsRef<'bump, T> for Reference<'bump, T> {
    fn precise_as_ref(&self) -> &'bump T {
        self.maybe_precise_as_ref().unwrap()
    }
}

impl<'bump, T> AsRef<T> for Reference<'bump, T> {
    fn as_ref(&self) -> &T {
        self.precise_as_ref()
    }
}

impl<'bump, T: Ord> Ord for Reference<'bump, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            Ordering::Equal
        } else {
            Ord::cmp(self.as_inner(), other.as_inner())
        }
    }
}

impl<'bump, T:PartialOrd> PartialOrd for Reference<'bump, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else {
            PartialOrd::partial_cmp(self.as_inner(), other.as_inner())
        }
    }
}

impl<'b, T: Debug> Debug for Reference<'b, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'bump, T> MaybeInvalid for Reference<'bump, T> {
    fn is_valid(&self) -> bool {
        self.maybe_precise_as_ref().is_some()
    }
}

impl<'bump, T> From<&'bump Option<T>> for Reference<'bump, T> {
    fn from(value: &'bump Option<T>) -> Self {
        Self {
            inner: NonNull::from(value),
            lt: Default::default(),
        }
    }
}

impl<'bump, T> Clone for Reference<'bump, T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner,
            lt: Default::default(),
        }
    }
}

impl<'bump, T> Copy for Reference<'bump, T> {}

impl<'bump, T: Hash> Hash for Reference<'bump, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_option_ref().hash(state);
    }
}
