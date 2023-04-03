use std::{
    num::NonZeroUsize,
    sync::atomic::{self, AtomicUsize},
};

use thiserror::Error;

static N_LOCK: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug)]
pub struct IsLock {
    inner: AtomicUsize,
}

impl IsLock {
    pub fn is_free(&self) -> bool {
        self.as_usize() == 0
    }

    pub fn as_usize(&self) -> usize {
        self.inner.load(atomic::Ordering::Acquire)
    }

    pub fn freeze(&self) {
        self.inner.store(0, atomic::Ordering::SeqCst)
    }

    pub fn new() -> Self {
        let i = N_LOCK.fetch_add(1, atomic::Ordering::AcqRel);
        if i == usize::MAX {
            panic!(
                "too many locks, please try to use less than {} next time",
                usize::MAX
            )
        } else {
            IsLock {
                inner: AtomicUsize::new(i),
            }
        }
    }
}

impl PartialEq for IsLock {
    fn eq(&self, other: &Self) -> bool {
        self.as_usize() == other.as_usize()
    }
}
impl Eq for IsLock {}
impl Ord for IsLock {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_usize().cmp(&other.as_usize())
    }
}
impl PartialOrd for IsLock {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}
impl std::hash::Hash for IsLock {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_usize().hash(state);
    }
}
impl Clone for IsLock {
    fn clone(&self) -> Self {
        Self {
            inner: AtomicUsize::new(self.as_usize()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lock {
    content: NonZeroUsize,
}

impl Lock {
    pub fn is_correspinding_lock(&self, is_lock: &IsLock) -> bool {
        let l = is_lock.as_usize();
        l == 0 || l == self.content.get()
    }
}

#[derive(Debug, Error)]
pub enum LockError {
    #[error("Wrong lock")]
    WrongLock,
    #[error("Assignement points to nothing !!!")]
    NullPointer,
}
