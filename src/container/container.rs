use std::{
    cell::{RefCell, Ref},
    ptr::NonNull,
    sync::atomic::{self, AtomicU16},
};

use crate::{
    formula::{function::{InnerFunction, Function}, sort::InnerSort},
    problem::{cell::InnerMemoryCell, step::InnerStep},
    utils::{string_ref::StrRef, traits::RefNamed},
};

use super::allocator::Container;
use super::contained::Contained;
use hashbrown::HashSet;
use itertools::Itertools;
use log::error;

use std::fmt::Debug;

// type InnerContainer<'bump, T> = RefCell<Vec<&'bump RefPointee<'bump, T>>>;

pub struct ScopedContainer<'bump> {
    sorts: RefCell<Vec<NonNull<Option<InnerSort<'bump>>>>>,
    functions: RefCell<Vec<NonNull<Option<InnerFunction<'bump>>>>>,
    steps: RefCell<Vec<NonNull<Option<InnerStep<'bump>>>>>,
    cells: RefCell<Vec<NonNull<Option<InnerMemoryCell<'bump>>>>>,
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
            fn allocate_pointee(
                &'bump self,
                content: Option<$inner<'bump>>,
            ) -> NonNull<Option<$inner>> {
                let uninit_ref = NonNull::from(Box::leak(Box::new(content)));
                self.$fun.borrow_mut().push(uninit_ref);
                uninit_ref
            }
        }
    };
}

make_scope_allocator!(functions, Function, InnerFunction);
impl<'bump> Container<'bump, InnerSort<'bump>> for ScopedContainer<'bump> {
    fn allocate_pointee(
        &'bump self,
        content: Option<InnerSort<'bump>>,
    ) -> NonNull<Option<InnerSort>> {
        let uninit_ref = NonNull::from(Box::leak(Box::new(content)));
        self.sorts.borrow_mut().push(uninit_ref);
        uninit_ref
    }
}
make_scope_allocator!(steps, Step, InnerStep);
make_scope_allocator!(cells, MemoryCell, InnerMemoryCell);

macro_rules! my_drop {
    ($($fun:ident),*) => {
        $(
            for e in $fun.get_mut() {
                drop(unsafe { Box::from_raw(e.as_mut()) });
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

// macro_rules! make_into_iters {
//     ($name:ident, $out:ident, $inner:ident, $bump:lifetime) => {
//         paste! {
//             pub(crate) fn [< $name _into_iter >]<'a> (
//                 &'a self,
//             ) -> VecRefWrapperMap<
//                 'a,
//                 &$bump Option<$inner<$bump>>,
//                 $out<'bump>,
//                 fn(&&Option<$inner<$bump>>) -> $out<$bump>,
//             > where 'bump:'a {
//                 VecRefWrapperMap {
//                     r: self.$name.borrow(),
//                     f: |i| $out::<$bump>::from_ref(*i),
//                 }
//             }
//         }
//     };
// }

static UNIQUE_FUNCTIONS: AtomicU16 = AtomicU16::new(0);

impl<'bump> ScopedContainer<'bump> {
    /// find a name starting by `name` that isn't assigned to any function yet
    pub fn find_free_function_name(&self, name: &str) -> String {
        let id = UNIQUE_FUNCTIONS.fetch_add(1, atomic::Ordering::AcqRel);
        format!("_{id:?}${name}")
    }

    pub fn is_name_available(&'bump self, name: &str) -> bool {
        // self.functions_into_iter()
        //     .into_iter()
        //     .all(|f| f.name().as_ref() != name)
        //     && self.sorts_into_iter().into_iter().all(|s| s.name() != name)
        //     && self.steps_into_iter().into_iter().all(|s| s.name() != name)
        //     && self.cells_into_iter().into_iter().all(|c| c.name() != name)
        self.name_hash_set().contains(name)
    }

    pub fn name_hash_set<'a>(&'bump self) -> HashSet<StrRef<'a>>
    where
        'bump: 'a,
    {
        // let f_iter = self.functions_into_iter();
        // let sort_iter = self.sorts_into_iter();
        // let step_iter = self.steps_into_iter();
        // let cell_iter = self.cells_into_iter();

        // chain!(
        //     f_iter.into_iter().map(|f| f.name().into()),
        //     sort_iter.into_iter().map(|s| s.name().into()),
        //     step_iter.into_iter().map(|s| s.name().into()),
        //     cell_iter.into_iter().map(|c| c.name().into()),
        // )
        // .collect()

        fn populate<'a, 'bump, T>(
            h: &mut HashSet<StrRef<'a>>,
            vec: &'a RefCell<Vec<NonNull<Option<T>>>>,
        ) where
            'bump: 'a,
            &'a T: RefNamed<'a>,
        {
            let vec = vec.borrow();
            h.extend(
                vec.iter()
                    .filter_map(|x| {
                        if super::PRINT_DEREF {
                            error!("deref NonNull at {} in {}", line!(), file!());
                        }
                        unsafe { x.as_ref() }.as_ref()
                    })
                    .map(|n| n.name_ref()),
            )
        }

        let mut h = HashSet::with_capacity(
            self.functions.borrow().len()
                + self.sorts.borrow().len()
                + self.cells.borrow().len()
                + self.steps.borrow().len(),
        );
        populate(&mut h, &self.functions);
        populate(&mut h, &self.sorts);
        populate(&mut h, &self.steps);
        populate(&mut h, &self.cells);
        h
    }

    // make_into_iters!(functions, Function, InnerFunction, 'bump);
    // make_into_iters!(sorts, Sort, InnerSort, 'bump);
    // make_into_iters!(steps, Step, InnerStep, 'bump);
    // make_into_iters!(cells, MemoryCell, InnerMemoryCell, 'bump);

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

    pub fn get_functions_vec_filtered<F>(&'bump self, f:F) -> Vec<Function<'bump>> where F:Fn(&Function<'bump>) -> bool {
        let function = self.functions.borrow();
        function.iter().map(|f| 
            Function::from_raw(*f, Default::default())
        ).filter(f).collect_vec()
    }
}

pub struct StaticContainer;

impl<I> Container<'static, I> for StaticContainer
where
    I: Contained<'static> + 'static,
{
    fn allocate_pointee(&'static self, content: Option<I>) -> NonNull<Option<I>> {
        NonNull::from(Box::leak(Box::new(content)))
    }
}
