pub mod builtins;
// pub mod collection;
pub mod sort_proxy;
pub mod sorted;
use bitflags::bitflags;
use core::fmt::Debug;
use std::{cmp::Ordering, fmt::Display, hash::Hash, marker::PhantomData, ptr::NonNull};

use crate::{
    container::{CanBeAllocated, Container, FromNN, ScopeAllocator},
    environement::traits::{KnowsRealm, Realm},
    utils::precise_as_ref::PreciseAsRef,
};

bitflags! {
    #[derive(Default, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy )]
    pub struct SFlags: u32 {
        const TERM_ALGEBRA =        1<<0;
        const BUILTIN_VAMPIRE =     1<<1;
        const EVALUATABLE =         1<<2;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sort<'bump> {
    inner: NonNull<InnerSort<'bump>>,
    container: PhantomData<&'bump ()>,
}

unsafe impl<'bump> Sync for Sort<'bump> {}
unsafe impl<'bump> Send for Sort<'bump> {}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerSort<'bump> {
    inner: HiddenSort<'bump>,
}

impl<'bump> InnerSort<'bump> {
    fn new(name: String, flags: SFlags, evaluated: Option<Sort<'bump>>) -> Self {
        InnerSort {
            inner: HiddenSort {
                name,
                flags,
                evaluated,
            },
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct HiddenSort<'bump> {
    name: String,
    flags: SFlags,
    evaluated: Option<Sort<'bump>>,
}

impl<'a> Ord for Sort<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Ord::cmp(&Rc::as_ptr(&self.0), &Rc::as_ptr(&other.0))
        if self != other {
            Ord::cmp(self.name(), other.name())
                .then(Ord::cmp(&self.as_ptr_usize(), &self.as_ptr_usize()))
        } else {
            Ordering::Equal
        }
    }
}

impl<'a> PartialOrd for Sort<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

impl<'a> Display for Sort<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner().name)
    }
}

impl<'a> Hash for Sort<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ptr_usize().hash(state);
    }
}

impl<'a> Sort<'a> {
    // ~~~~~~~~~~~~~~~~~~ is ~~~~~~~~~~~~~~~~~~~~
    pub fn is_term_algebra(&self) -> bool {
        self.inner().flags.contains(SFlags::TERM_ALGEBRA)
    }

    pub fn is_built_in(&self) -> bool {
        self.inner().flags.contains(SFlags::BUILTIN_VAMPIRE)
    }

    pub fn is_evaluatable(&self) -> bool {
        let r = self.inner().flags.contains(SFlags::EVALUATABLE);
        assert_eq!(r, self.evaluated_sort().is_some());
        r
    }

    // ~~~~~~~~~~~~~~~ builders ~~~~~~~~~~~~~~~~~
    pub fn new(allocator: &'a Container<'a>, inner: InnerSort<'a>) -> Self {
        Self::allocate(allocator, inner)
    }

    pub fn new_regular(allocator: &'a Container<'a>, name: String) -> Self {
        Self::new(allocator, InnerSort::new(name, SFlags::empty(), None))
    }

    // ~~~~~~~~~~~~~~~~~ cast ~~~~~~~~~~~~~~~~~~~
    pub fn as_ptr_usize(&self) -> usize {
        self.inner() as *const HiddenSort as usize
    }

    fn inner(&self) -> &'a HiddenSort {
        self.precise_as_ref().as_ref()
    }

    pub fn as_sort(&self) -> Sort<'a> {
        *self
    }

    // ~~~~~~~~~~~~~~~~ other ~~~~~~~~~~~~~~~~~~~
    pub fn name(&self) -> &'a str {
        &self.precise_as_ref().inner.name
    }

    pub fn evaluated_sort(&self) -> Option<Sort<'a>> {
        self.as_ref().as_ref().evaluated
    }

    /// Equality modulo a [Realm]
    ///
    /// ```rust
    /// assert!(BOOL.eq_realm(CONDITION.as_ref(), Realm::Evaluated))
    /// ```
    pub fn eq_realm<R>(&self, other: &Self, realm: &R) -> bool
    where
        R: KnowsRealm,
    {
        (self == other)
            || match realm.get_realm() {
                Realm::Symbolic => false,
                Realm::Evaluated => {
                    self.is_evaluatable() && (self.evaluated_sort() == other.evaluated_sort())
                }
            }
    }
}

impl<'bump> AsRef<HiddenSort<'bump>> for InnerSort<'bump> {
    fn as_ref(&self) -> &HiddenSort<'bump> {
        &self.inner
    }
}

impl<'bump> PreciseAsRef<'bump, InnerSort<'bump>> for Sort<'bump> {
    fn precise_as_ref(&self) -> &'bump InnerSort<'bump> {
        unsafe { self.inner.as_ref() } // for self to exists, container must exists
    }
}

impl<'bump> AsRef<InnerSort<'bump>> for Sort<'bump> {
    fn as_ref(&self) -> &InnerSort<'bump> {
        self.precise_as_ref()
    }
}

impl<'bump> CanBeAllocated<'bump> for Sort<'bump> {
    type Inner = InnerSort<'bump>;

    fn allocate<A>(allocator: &'bump A, inner: Self::Inner) -> Self
    where
        A: ScopeAllocator<'bump, Self::Inner> + 'bump,
    {
        let inner = unsafe {
            let ptr = allocator.alloc();
            std::ptr::write(ptr.as_ptr(), inner);
            ptr
        };
        Sort {
            inner,
            container: PhantomData::default(),
        }
    }
}

impl<'bump> From<&'bump InnerSort<'bump>> for Sort<'bump> {
    fn from(value: &'bump InnerSort<'bump>) -> Self {
        Sort {
            inner: NonNull::from(value),
            container: Default::default(),
        }
    }
}

impl<'bump> FromNN<'bump> for Sort<'bump> {
    type Inner = InnerSort<'bump>;

    unsafe fn from_nn(inner: NonNull<Self::Inner>) -> Self {
        Self {
            inner,
            container: Default::default(),
        }
    }
}

pub fn new_static_sort(
    name: &str,
    flags: SFlags,
    evaluated: Option<Sort<'static>>,
) -> Sort<'static> {
    let inner = NonNull::new(Box::into_raw(Box::new(InnerSort::new(
        name.to_owned(),
        flags,
        evaluated,
    ))))
    .unwrap();
    Sort {
        inner,
        container: Default::default(),
    }
}
