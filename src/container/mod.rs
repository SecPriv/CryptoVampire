use itertools::chain;
use paste::paste;
use std::{
    cell::{Ref, RefCell},
    collections::HashSet,
    fmt::Debug,
    iter::Map,
    ops::DerefMut,
    ptr::NonNull,
    slice::Iter,
};

mod container;
pub use container::ScopedContainer;
pub mod allocator;
pub mod reference;
pub mod utils;

use crate::{
    assert_variance,
    formula::{
        function::{Function, InnerFunction},
        sort::{InnerSort, Sort},
    },
    problem::{
        cell::{InnerMemoryCell, MemoryCell},
        step::{InnerStep, Step},
    },
    utils::string_ref::StrRef,
};

pub trait ScopeAllocator<'bump, T> {
    unsafe fn alloc(&'bump self) -> NonNull<T>;
}

pub trait CanBeAllocated<'bump> {
    type Inner;
    fn allocate<A>(allocator: &'bump A, inner: Self::Inner) -> Self
    where
        A: ScopeAllocator<'bump, Self::Inner> + 'bump;
}

unsafe fn aux_alloc<T>(mut vec: impl DerefMut<Target = Vec<NonNull<T>>>) -> NonNull<T> {
    // let ptr = NonNull::new_unchecked(alloc(Layout::new::<T>()) as *mut T);
    let ptr = NonNull::dangling();
    vec.push(ptr);
    ptr
}

macro_rules! make_scope_allocator {
    ($fun:ident, $t:ty) => {
        impl<'bump> ScopeAllocator<'bump, $t> for Container<'bump> {
            unsafe fn alloc(&'bump self) -> NonNull<$t> {
                aux_alloc(self.$fun.borrow_mut())
            }
        }
    };
}

// assert_variance!(Container);
