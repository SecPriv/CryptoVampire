use std::{cell::RefCell, ops::DerefMut, ptr::NonNull};

use super::{function::InnerFunction, sort::InnerSort};

// #[derive(Debug)]
pub struct Container<'bump> {
    sorts: RefCell<Vec<NonNull<InnerSort>>>,
    functions: RefCell<Vec<NonNull<InnerFunction<'bump>>>>,
}

pub trait ScopeAllocator<T> {
    unsafe fn alloc(&self) -> NonNull<T>;
}

pub trait CanBeAllocated<'bump> {
    type Inner;
    fn allocate<A>(allocator: &'bump A, inner: Self::Inner) -> Self
    where
        A: ScopeAllocator<Self::Inner> + 'bump;
}

unsafe fn aux_alloc<T>(mut vec: impl DerefMut<Target = Vec<NonNull<T>>>) -> NonNull<T> {
    // let ptr = NonNull::new_unchecked(alloc(Layout::new::<T>()) as *mut T);
    let ptr = NonNull::dangling();
    vec.push(ptr);
    ptr
}

impl<'bump> ScopeAllocator<InnerSort> for Container<'bump> {
    unsafe fn alloc(&self) -> NonNull<InnerSort> {
        aux_alloc(self.sorts.borrow_mut())
    }
}

impl<'bump> ScopeAllocator<InnerFunction<'bump>> for Container<'bump> {
    unsafe fn alloc(&self) -> NonNull<InnerFunction<'bump>> {
        aux_alloc(self.functions.borrow_mut())
    }
}

impl<'bump> Drop for Container<'bump> {
    fn drop(&mut self) {
        let Container { sorts, functions } = self;
        for s in sorts.get_mut() {
            drop(unsafe { s.as_mut() })
        }
        for fun in functions.get_mut() {
            drop(unsafe { fun.as_mut() })
        }
    }
}
