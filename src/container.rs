use std::{cell::RefCell, fmt::Debug, ops::DerefMut, ptr::NonNull};

use crate::{
    formula::{function::InnerFunction, sort::InnerSort},
    problem::{cell::InnerMemoryCell, step::InnerStep},
};

type InnerContainer<T> = RefCell<Vec<NonNull<T>>>;

// #[derive(Debug)]
pub struct Container<'bump> {
    sorts: InnerContainer<InnerSort>,
    functions: InnerContainer<InnerFunction<'bump>>,
    steps: InnerContainer<InnerStep<'bump>>,
    cells: InnerContainer<InnerMemoryCell<'bump>>,
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

// impl<'bump> ScopeAllocator<InnerSort> for Container<'bump> {
//     unsafe fn alloc(&self) -> NonNull<InnerSort> {
//         aux_alloc(self.sorts.borrow_mut())
//     }
// }

// impl<'bump> ScopeAllocator<InnerFunction<'bump>> for Container<'bump> {
//     unsafe fn alloc(&self) -> NonNull<InnerFunction<'bump>> {
//         aux_alloc(self.functions.borrow_mut())
//     }
// }

macro_rules! make_scope_allocator {
    ($fun:ident, $t:ty) => {
        impl<'bump> ScopeAllocator<$t> for Container<'bump> {
            unsafe fn alloc(&self) -> NonNull<$t> {
                aux_alloc(self.$fun.borrow_mut())
            }
        }
    };
}

make_scope_allocator!(functions, InnerFunction<'bump>);
make_scope_allocator!(sorts, InnerSort);
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
