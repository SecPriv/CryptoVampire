use std::{cell::UnsafeCell, cmp::Ordering, hash::Hash, marker::PhantomData, ptr::NonNull};

#[derive(Debug)]
struct InnerContent<A, B> {
    immutable: A,
    // hash ref to the cell iff has ref to ContentHoled
    mutable: UnsafeCell<B>,
}

#[derive(Copy, Debug)]
pub struct Content<'a, A, B, F> {
    inner: &'a InnerContent<A, B>,
    lock: PhantomData<ContentLock<A, B, F>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct InnerContentRef<'a, A, B, F> {
    pub immutable: &'a A,
    pub mutable: &'a B,
    lock: PhantomData<&'a ContentLock<A, B, F>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InnerContentMutRef<'a, A, B, F> {
    pub immutable: &'a A,
    pub mutable: &'a mut B,
    lock: PhantomData<&'a mut ContentLock<A, B, F>>,
}

pub struct ContentHolder<A, B, F> {
    content: UnsafeCell<Vec<NonNull<InnerContent<A, B>>>>,
    lock: PhantomData<F>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentLock<A, B, F> {
    lock: PhantomData<ContentHolder<A, B, F>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MainLock<A, B, F> {
    lock: PhantomData<ContentHolder<A, B, F>>,
}

// impl

impl<A, B, F> ContentHolder<A, B, F> {
    /// safe so long a exists, lives 'a and belongs to a ContentHolder<A, B, F>
    unsafe fn content_from_nonnull<'a>(a: NonNull<InnerContent<A, B>>) -> Content<'a, A, B, F> {
        Content {
            inner: a.as_ref(),
            lock: Default::default(),
        }
    }

    pub fn new_with_lock(_f: F) -> (Self, MainLock<A, B, F>, ContentLock<A, B, F>) {
        let c = Default::default();
        let cl = ContentLock {
            lock: Default::default(),
        };
        let ml = MainLock {
            lock: Default::default(),
        };
        (c, ml, cl)
    }

    pub fn add<'a>(&'a self, _: &mut MainLock<A, B, F>, imm: A, m: B) -> Content<'a, A, B, F> {
        let c = unsafe {
            NonNull::new_unchecked(Box::into_raw(Box::new(InnerContent {
                immutable: imm,
                mutable: UnsafeCell::new(m),
            })))
        };

        // controled by l
        unsafe { &mut *self.content.get() }.push(c);
        unsafe { Self::content_from_nonnull(c) }
    }

    pub fn get<'a, 'b>(
        &'a self,
        _: &'b MainLock<A, B, F>,
        i: usize,
    ) -> Option<Content<'a, A, B, F>> {
        unsafe { &*self.content.get() }
            .get(i)
            .map(|&a| unsafe { Self::content_from_nonnull(a) })
    }

    pub fn iter<'a, 'b>(
        &'a self,
        _: &'b MainLock<A, B, F>,
    ) -> impl Iterator<Item = Content<'a, A, B, F>> + 'b {
        unsafe { &*self.content.get() }
            .iter()
            .map(|&a| unsafe { Self::content_from_nonnull(a) })
    }
}

impl<'a, 'b, A, B, F> Content<'a, A, B, F>
where
    'a: 'b,
{
    pub fn get_inner_mut_as_ref(
        &self,
        _owner: &'b ContentLock<A, B, F>,
    ) -> InnerContentRef<'b, A, B, F>
    where
        'a: 'b,
    {
        InnerContentRef {
            immutable: &self.inner.immutable,
            mutable: unsafe { &*self.inner.mutable.get() },
            lock: Default::default(),
        }
    }

    pub fn get_inner_mut_as_mut_ref(
        &self,
        _owner: &'b mut ContentLock<A, B, F>,
    ) -> InnerContentMutRef<'b, A, B, F> {
        InnerContentMutRef {
            immutable: &self.inner.immutable,
            mutable: unsafe { &mut *self.inner.mutable.get() },
            lock: Default::default(),
        }
    }
}

// generic impl

impl<A, B, F> Default for ContentHolder<A, B, F> {
    fn default() -> Self {
        Self {
            content: Default::default(),
            lock: Default::default(),
        }
    }
}

impl<A: PartialEq, B> PartialEq for InnerContent<A, B> {
    fn eq(&self, other: &Self) -> bool {
        self.immutable == other.immutable
    }
}

impl<A: PartialOrd, B> PartialOrd for InnerContent<A, B> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.immutable.partial_cmp(&other.immutable)
    }
}

impl<A: Ord, B> Ord for InnerContent<A, B> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.immutable.cmp(&other.immutable)
    }
}

impl<A: Eq, B> Eq for InnerContent<A, B> {}

impl<A: Hash, B> Hash for InnerContent<A, B> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.immutable.hash(state);
    }
}

impl<'a, A, B, F> PartialEq for Content<'a, A, B, F> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(&self.inner, &other.inner)
    }
}

impl<'a, A: PartialOrd, B, F> PartialOrd for Content<'a, A, B, F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else {
            self.inner.partial_cmp(&other.inner)
        }
    }
}

impl<'a, A: Ord, B, F> Ord for Content<'a, A, B, F> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(&other).unwrap()
    }
}

impl<'a, A, B, F> Eq for Content<'a, A, B, F> {}

impl<'a, A: Hash, B: Hash, F> Hash for Content<'a, A, B, F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

impl<'a, A, B, F> Clone for Content<'a, A, B, F> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner,
            lock: Default::default(),
        }
    }
}
