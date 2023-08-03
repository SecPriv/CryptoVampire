use std::{cell::RefCell, ptr::NonNull};

use crate::{
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

use super::{allocator::Container, reference::Reference};
use super::{contained::Contained, utils::VecRefWrapperMap};
use hashbrown::HashSet;
use itertools::chain;
use paste::paste;
use std::fmt::Debug;

// type InnerContainer<'bump, T> = RefCell<Vec<&'bump RefPointee<'bump, T>>>;

pub struct ScopedContainer<'bump> {
    sorts: RefCell<Vec<&'bump Option<InnerSort<'bump>>>>,
    functions: RefCell<Vec<&'bump Option<InnerFunction<'bump>>>>,
    steps: RefCell<Vec<&'bump Option<InnerStep<'bump>>>>,
    cells: RefCell<Vec<&'bump Option<InnerMemoryCell<'bump>>>>,
}

// unsafe fn aux_alloc<T>(mut vec: impl DerefMut<Target = Vec<NonNull<T>>>) -> NonNull<T> {
//     // let ptr = NonNull::new_unchecked(alloc(Layout::new::<T>()) as *mut T);
//     let ptr = NonNull::dangling();
//     vec.push(ptr);
//     ptr
// }

macro_rules! make_scope_allocator {
    ($fun:ident, $t:ident, $inner:ident) => {
        impl<'bump> Container<'bump, $inner<'bump>> for ScopedContainer<'bump> {
            fn allocate_pointee(&'bump self, content: Option<$inner<'bump>>) -> &'bump Option<$inner> {
                let uninit_ref = &*Box::leak(Box::new(content));
                self.$fun.borrow_mut().push(uninit_ref);
                uninit_ref
            }
        }
    };
}

make_scope_allocator!(functions, Function, InnerFunction);
make_scope_allocator!(sorts, Sort, InnerSort);
make_scope_allocator!(steps, Step, InnerStep);
make_scope_allocator!(cells, MemoryCell, InnerMemoryCell);

macro_rules! my_drop {
    ($($fun:ident),*) => {
        $(
            for e in $fun.get_mut() {
                unsafe { std::ptr::drop_in_place(e as *mut _) }
            }
        )*
    };
}

impl<'bump> Drop for ScopedContainer<'bump> {
    fn drop(&mut self) {
        let ScopedContainer {
            sorts,
            functions,
            steps,
            cells,
        } = self;
        my_drop!(sorts, functions, cells, steps);
    }
}

impl<'bump> Debug for ScopedContainer<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Container")
            .field("sorts", &self.sorts.try_borrow())
            .field("functions", &self.functions.try_borrow())
            .field("steps", &self.steps.try_borrow())
            .field("cells", &self.cells.try_borrow())
            .finish()
    }
}

macro_rules! make_into_iters {
    ($name:ident, $out:ident, $inner:ident, $bump:lifetime) => {
        paste! {
            pub(crate) fn [< $name _into_iter >]<'a> (
                &'a self,
            ) -> VecRefWrapperMap<
                'a,
                &$bump Option<$inner<$bump>>,
                $out<'bump>,
                fn(&&Option<$inner<$bump>>) -> $out<$bump>,
            > {
                // VecRefWrapperMap {
                //     r: self.$name.borrow(),
                //     f: |i| $out::<$bump>::from_ref(*i),
                // }
                todo!()
            }
        }
    };
}

impl<'bump> ScopedContainer<'bump> {
    /// find a name starting by `name` that isn't assigned to any function yet
    pub fn find_free_function_name(&self, name: &str) -> String {
        // self.functions
        //     .borrow()
        //     .iter()
        //     .map(|nn| Function::from_ptr_inner(*nn))
        self.functions_into_iter()
            .into_iter()
            .filter_map(|f| {
                f.name()
                    .strip_prefix(name)
                    .and_then(|s| usize::from_str_radix(s, 10).ok())
            })
            .max()
            .map(|m| format!("{}{}", name, m + 1))
            .unwrap_or(name.to_owned())
    }

    pub fn is_name_available(&'bump self, name: &str) -> bool {
        self.functions_into_iter()
            .into_iter()
            .all(|f| f.name().as_ref() != name)
            && self.sorts_into_iter().into_iter().all(|s| s.name() != name)
            && self.steps_into_iter().into_iter().all(|s| s.name() != name)
            && self.cells_into_iter().into_iter().all(|c| c.name() != name)
    }

    pub fn name_hash_set<'a>(&'bump self) -> HashSet<StrRef<'a>>
    where
        'bump: 'a,
    {
        let f_iter = self.functions_into_iter();
        let sort_iter = self.sorts_into_iter();
        let step_iter = self.steps_into_iter();
        let cell_iter = self.cells_into_iter();

        chain!(
            f_iter.into_iter().map(|f| f.name().into()),
            sort_iter.into_iter().map(|s| s.name().into()),
            step_iter.into_iter().map(|s| s.name().into()),
            cell_iter.into_iter().map(|c| c.name().into()),
        )
        .collect()
    }

    make_into_iters!(functions, Function, InnerFunction, 'bump);
    make_into_iters!(sorts, Sort, InnerSort, 'bump);
    make_into_iters!(steps, Step, InnerStep, 'bump);
    make_into_iters!(cells, MemoryCell, InnerMemoryCell, 'bump);

    /// Creates a new [Container]
    ///
    /// ## Safety
    /// the lifetime is arbitrary, and therefore usafe.
    ///
    /// Any `'a` shorter that the lifetime of the container is fine.
    /// Since achieving this requires some "convicing" of borrow checker,
    /// favor using [scoped()] or [Self::new_leaked()].
    pub unsafe fn new_unbounded<'a>() -> ScopedContainer<'a> {
        ScopedContainer {
            sorts: Default::default(),
            functions: Default::default(),
            steps: Default::default(),
            cells: Default::default(),
        }
    }

    pub fn new_leaked() -> &'static mut Self {
        let container = unsafe { Self::new_unbounded() };
        Box::leak(Box::new(container))
    }

    /// Give a scope in which one can use a [Container]
    pub fn scoped<F, U>(f: F) -> U
    where
        F: for<'a> FnOnce(&'a mut ScopedContainer<'a>) -> U,
    {
        fn shorten_life<'a, 'short, 'long>(
            x: &'a mut ScopedContainer<'long>,
        ) -> &'a mut ScopedContainer<'short>
        where
            'long: 'short,
        {
            // this if the content lives at least 'bump, then it leaves at least 'short
            unsafe { std::mem::transmute(x) }
        }
        unsafe {
            let mut container = ScopedContainer::new_unbounded();
            let result = f(shorten_life(&mut container));
            drop(container); // result can't refer to anything in container, it can be safely dropped
            result
        }
    }
}

pub struct StaticContainer;

impl<I> Container<'static, I> for StaticContainer
where
    I: Contained<'static> + 'static,
{
    fn allocate_pointee(&'static self, content: Option<I>) -> &'static Option<I> {
        Box::leak(Box::new(content))
    }
}
