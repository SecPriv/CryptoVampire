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
pub use container::{ScopedContainer, StaticContainer};
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

// pub trait ScopeAllocator<'bump, T> {
//     unsafe fn alloc(&'bump self) -> NonNull<T>;
// }

// pub trait CanBeAllocated<'bump> {
//     type Inner;
//     fn allocate<A>(allocator: &'bump A, inner: Self::Inner) -> Self
//     where
//         A: ScopeAllocator<'bump, Self::Inner> + 'bump;
// }

// assert_variance!(Container);
