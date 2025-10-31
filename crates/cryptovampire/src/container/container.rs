use std::fmt::Debug;
use std::ptr::NonNull;
use std::sync::Mutex;
use std::sync::atomic::{self, AtomicU16};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use log::error;
use utils::string_ref::StrRef;
use utils::traits::RefNamed;

use super::allocator::Container;
use super::contained::Contained;
use crate::formula::function::builtin::BUILT_IN_FUNCTIONS;
use crate::formula::function::{Function, InnerFunction};
use crate::formula::sort::InnerSort;
use crate::problem::cell::InnerMemoryCell;
use crate::problem::step::InnerStep;

// type InnerContainer<'bump, T> = RefCell<Vec<&'bump RefPointee<'bump, T>>>;

pub struct ScopedContainer<'bump> {
    sorts: Mutex<Vec<NonNull<Option<InnerSort<'bump>>>>>,
    functions: Mutex<Vec<NonNull<Option<InnerFunction<'bump>>>>>,
    steps: Mutex<Vec<NonNull<Option<InnerStep<'bump>>>>>,
    cells: Mutex<Vec<NonNull<Option<InnerMemoryCell<'bump>>>>>,
}
unsafe impl<'bump> Sync for ScopedContainer<'bump> {}

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
            ) -> NonNull<Option<$inner<'bump>>> {
                let uninit_ref = NonNull::from(Box::leak(Box::new(content)));
                self.$fun.lock().expect("poisoned mutex").push(uninit_ref);
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
    ) -> NonNull<Option<InnerSort<'bump>>> {
        let uninit_ref = NonNull::from(Box::leak(Box::new(content)));
        self.sorts.lock().expect("poisoned mutex").push(uninit_ref);
        uninit_ref
    }
}
make_scope_allocator!(steps, Step, InnerStep);
make_scope_allocator!(cells, MemoryCell, InnerMemoryCell);

macro_rules! my_drop {
    ($($fun:ident),*) => {
        $(
            for e in $fun.lock().expect("poisoned mutex").iter_mut() {
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
            .field("sorts", &self.sorts.lock().expect("poisoned mutex"))
            .field("functions", &self.functions.lock().expect("poisoned mutex"))
            .field("steps", &self.steps.lock().expect("poisoned mutex"))
            .field("cells", &self.cells.lock().expect("poisoned mutex"))
            .finish()
    }
}

static UNIQUE_FUNCTIONS: AtomicU16 = AtomicU16::new(0);

impl<'bump> ScopedContainer<'bump> {
    /// find a name starting by `name` that isn't assigned to any function yet
    pub fn find_free_function_name(&self, name: &str) -> String {
        let id = UNIQUE_FUNCTIONS.fetch_add(1, atomic::Ordering::AcqRel);
        format!("_{id:?}${name}")
    }

    pub fn is_name_available(&'bump self, name: &str) -> bool {
        self.name_hash_set().contains(name)
    }

    pub fn name_hash_set<'a>(&'bump self) -> HashSet<StrRef<'a>>
    where
        'bump: 'a,
    {
        fn populate<'a, 'bump, T>(
            h: &mut HashSet<StrRef<'a>>,
            vec: &'a Mutex<Vec<NonNull<Option<T>>>>,
        ) where
            'bump: 'a,
            &'a T: RefNamed<'a>,
        {
            let vec = vec.lock().expect("poisoned mutex");
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
            self.functions.lock().expect("poisoned mutex").len()
                + self.sorts.lock().expect("poised mutex").len()
                + self.cells.lock().expect("poised mutex").len()
                + self.steps.lock().expect("poised mutex").len(),
        );
        populate(&mut h, &self.functions);
        populate(&mut h, &self.sorts);
        populate(&mut h, &self.steps);
        populate(&mut h, &self.cells);
        h
    }

    pub fn get_function_hash_map(&self) -> HashMap<StrRef<'bump>, Function<'bump>> {
        let functions = self.functions.lock().expect("poisoned mutex").clone();
        functions
            .into_iter()
            .map(|f| Function::from_raw(f, Default::default()))
            .chain(BUILT_IN_FUNCTIONS.iter().copied())
            .map(|f| (f.name(), f))
            .collect()
    }

    /// Creates a new [Container]
    ///
    /// ## Safety
    /// the lifetime is arbitrary, and therefore usafe.
    ///
    /// Any `'a` shorter that the lifetime of the container is fine.
    /// Since achieving this requires some "convicing" of borrow checker,
    /// favor using [Self::scoped()] or [Self::new_leaked()].
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

    pub fn get_functions_vec_filtered<F>(&'bump self, f: F) -> Vec<Function<'bump>>
    where
        F: Fn(&Function<'bump>) -> bool,
    {
        let function = self.functions.lock().expect("poisoned mutex").clone();
        function
            .iter()
            .map(|f| Function::from_raw(*f, Default::default()))
            .filter(f)
            .collect_vec()
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
