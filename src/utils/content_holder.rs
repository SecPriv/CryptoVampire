use std::{cell::UnsafeCell, cmp::Ordering, hash::Hash, marker::PhantomData};

#[derive(Debug)]
struct InnerContent<A, B> {
    immutable: A,
    // hash ref to the cell iff has ref to ContentHoled
    mutable: UnsafeCell<B>,
}

#[derive(Copy, Debug)]
pub struct Content<'a, A, B, F> {
    inner: &'a InnerContent<A, B>,
    lock: PhantomData<ContentHolder<A, B, F>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct InnerContentRef<'a, A, B, F> {
    pub immutable: &'a A,
    pub mutable: &'a B,
    lock: PhantomData<&'a ContentHolder<A, B, F>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InnerContentMutRef<'a, A, B, F> {
    pub immutable: &'a A,
    pub mutable: &'a mut B,
    lock: PhantomData<&'a mut ContentHolder<A, B, F>>,
}

pub struct ContentHolder<A, B, F> {
    content: Vec<*const InnerContent<A, B>>,
    lock: F,
}

// impl

impl<A, B, F> 

impl<'a, A, B, F> Content<'a, A, B, F> {
    pub fn get_inner_mut_as_ref(
        &self,
        _owner: &'a ContentHolder<A, B, F>,
    ) -> InnerContentRef<'a, A, B, F> {
        InnerContentRef {
            immutable: &self.inner.immutable,
            mutable: unsafe { &*self.inner.mutable.get() },
            lock: Default::default()
        }
    }
    
    pub fn get_inner_mut_as_mut_ref(
        &self,
        _owner: &'a mut ContentHolder<A, B, F>,
    ) -> InnerContentMutRef<'a, A, B, F> {
        InnerContentMutRef {
            immutable: &self.inner.immutable,
            mutable: unsafe { &mut *self.inner.mutable.get() },
            lock: Default::default()
        }
    }
}

// generic impl

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
