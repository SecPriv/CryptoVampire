use core::sync::atomic::Ordering::*;
use std::hash::Hash;
use std::ptr::NonNull;
use std::sync::atomic::AtomicUsize;

use serde::Serialize;

/// more or less [Arc] that can point to a static point and thus be cloned in
/// static. Moreover, equality and hash comes from the pointer
pub struct SmartCow<U>(NonNull<InnerSmartCow<U>>);

#[derive(Debug, Serialize)]
pub struct InnerSmartCow<U> {
    count: Option<AtomicUsize>,
    content: U,
}

impl<U> SmartCow<U> {
    pub const fn from_static(content: &'static InnerSmartCow<U>) -> Self {
        assert!(content.count.is_none());
        Self(NonNull::from_ref(content))
    }

    pub const fn const_clone(&self) -> Self {
        assert!(self.is_static());
        Self(self.0)
    }

    pub fn new(content: U) -> Self {
        let inner = InnerSmartCow {
            count: Some(AtomicUsize::new(1)),
            content,
        };
        Self(NonNull::from_ref(Box::leak(Box::new(inner))))
    }

    pub const fn as_ref(&self) -> &U {
        &self.as_inner_ref().content
    }

    const fn as_inner_ref(&self) -> &InnerSmartCow<U> {
        unsafe { self.0.as_ref() }
    }

    pub fn as_usize(&self) -> usize {
        self.0.as_ptr() as usize
    }

    pub const fn is_static(&self) -> bool {
        self.as_inner_ref().count.is_none()
    }
}

impl<U> InnerSmartCow<U> {
    pub const fn mk_static(content: U) -> Self {
        Self {
            count: None,
            content,
        }
    }
}

impl<U> PartialEq for SmartCow<U> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<U> Eq for SmartCow<U> {}

impl<U> Hash for SmartCow<U> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

#[allow(clippy::non_canonical_partial_ord_impl)]
impl<U: PartialOrd> PartialOrd for SmartCow<U> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self == other {
            Some(std::cmp::Ordering::Equal)
        } else {
            let ret = self.0.partial_cmp(&other.0)?;
            assert!(!ret.is_eq());
            Some(ret)
        }
    }
}

impl<U: PartialOrd> Ord for SmartCow<U> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            std::cmp::Ordering::Equal
        } else {
            let ret = self.0.cmp(&other.0);
            assert!(!ret.is_eq());
            ret
        }
    }
}

impl<U> Clone for SmartCow<U> {
    fn clone(&self) -> Self {
        let inner = self.as_inner_ref();
        if let Some(c) = &inner.count {
            // same implementation as `Arc` hence why the `Rela`
            let old_count = c.fetch_add(1, Relaxed);

            #[allow(clippy::absurd_extreme_comparisons)] // clearer semantically
            if old_count >= usize::MAX {
                panic!("too many references for the counter")
            }
        }
        Self(self.0)
    }
}

impl<U> Drop for SmartCow<U> {
    fn drop(&mut self) {
        // same implementation as `Arc`
        {
            let inner = self.as_inner_ref();
            let Some(count) = &inner.count else {
                return;
            };

            if count.fetch_sub(1, Release) != 1 {
                return;
            }
            std::sync::atomic::fence(Acquire);
        }

        let inner = unsafe { Box::from_raw(self.0.as_mut()) };
        drop(inner);
    }
}

unsafe impl<U: Sync> Sync for SmartCow<U> {}
unsafe impl<U: Sync> Send for SmartCow<U> {}

impl<U: Serialize> Serialize for SmartCow<U> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.as_inner_ref().serialize(serializer)
    }
}
