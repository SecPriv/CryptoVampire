mod container;
pub use container::{ScopedContainer, StaticContainer};
pub mod allocator;
pub mod contained;
pub mod reference;
pub mod utils;

const PRINT_DEREF: bool = false;

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
