use std::{cell::RefCell, fmt::Debug, ops::DerefMut, ptr::NonNull};

use itertools::Itertools;

use crate::{
    formula::{
        function::{Function, InnerFunction},
        sort::InnerSort,
    },
    problem::{cell::InnerMemoryCell, step::InnerStep},
};

type InnerContainer<T> = RefCell<Vec<NonNull<T>>>;

// #[derive(Debug)]
pub struct Container<'bump> {
    sorts: InnerContainer<InnerSort<'bump>>,
    functions: InnerContainer<InnerFunction<'bump>>,
    steps: InnerContainer<InnerStep<'bump>>,
    cells: InnerContainer<InnerMemoryCell<'bump>>,
}

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

make_scope_allocator!(functions, InnerFunction<'bump>);
make_scope_allocator!(sorts, InnerSort<'bump>);
make_scope_allocator!(steps, InnerStep<'bump>);
make_scope_allocator!(cells, InnerMemoryCell<'bump>);

macro_rules! my_drop {
    ($($fun:ident),*) => {
        $(
            for e in $fun.get_mut() {
                drop(unsafe { e.as_mut()})
            }
        )*
    };
}

impl<'bump> Drop for Container<'bump> {
    fn drop(&mut self) {
        let Container {
            sorts,
            functions,
            steps,
            cells,
        } = self;
        my_drop!(sorts, functions, cells, steps);
    }
}

impl<'bump> Debug for Container<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Container")
            .field("sorts", &self.sorts.borrow())
            .field("functions", &self.functions.borrow())
            .field("steps", &self.steps.borrow())
            .field("cells", &self.cells.borrow())
            .finish()
    }
}

impl<'bump> Container<'bump> {
    /// find a name starting by `name` that isn't assigned to any function yet
    pub fn find_free_function_name(&self, name: &str) -> String {
        self.functions
            .borrow()
            .iter()
            .map(|nn| Function::from_ptr_inner(*nn))
            .filter_map(|f| {
                f.name()
                    .strip_prefix(name)
                    .and_then(|s| usize::from_str_radix(s, 10).ok())
            })
            .max()
            .map(|m| format!("{}{}", name, m + 1))
            .unwrap_or(name.to_owned())
    }
}
