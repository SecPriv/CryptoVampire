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
                unsafe { std::ptr::drop_in_place(e.as_ptr()) }
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

macro_rules! make_into_iters {
    ($name:ident, $out:ty, $bump:lifetime) => {
        paste! {
            pub(crate) fn [< $name _into_iter >] (
                & $bump self,
            ) -> VecRefWrapperMap<
                $bump,
                NonNull<<$out as FromNN<$bump>>::Inner >,
                $out,
                fn(&NonNull<<$out as FromNN<$bump>>::Inner>) -> $out,
            > {
                VecRefWrapperMap {
                    r: self.$name.borrow(),
                    f: |nn| unsafe { <$out as FromNN<$bump>>::from_nn(*nn) },
                }
            }
        }
    };
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

    make_into_iters!(functions, Function<'bump>, 'bump);
    make_into_iters!(sorts, Sort<'bump>, 'bump);
    make_into_iters!(steps, Step<'bump>, 'bump);
    make_into_iters!(cells, MemoryCell<'bump>, 'bump);

    unsafe fn new_unbounded<'a>() -> Container<'a> {
        Container {
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

    /// uses [std::mem::transmute]...
    pub fn shorten_life<'short>(&'_ self) -> &'_ Container<'short>
    where
        'bump: 'short,
    {
        // this if the content lives at least 'bump, then it leaves at least 'short
        unsafe { std::mem::transmute(self) }
    }
}

pub fn scope<F, U>(f: F) -> U
where
    F: for<'bump> FnOnce(&'bump Container<'bump>) -> U,
{
    let container: Container<'static> = unsafe { Container::new_unbounded() };
    let result = f(&container.shorten_life());
    drop(container);
    result
}

pub trait NameFinder<T> {
    fn find_free_name(&self, name: &str) -> String;
}

impl<'bump> NameFinder<Function<'bump>> for Container<'bump> {
    fn find_free_name(&self, name: &str) -> String {
        self.find_free_function_name(name)
    }
}

pub(crate) trait FromNN<'bump>: Sized {
    type Inner;
    /// inner lives 'bump
    unsafe fn from_nn(inner: NonNull<Self::Inner>) -> Self;
}

/// from https://stackoverflow.com/a/33542412/10875409
#[derive(Debug)]
pub struct VecRefWrapperMap<'a, T: 'a, U, F>
where
    F: Fn(&'a T) -> U + Clone,
{
    r: Ref<'a, Vec<T>>,
    f: F,
}

impl<'a, 'b: 'a, T: 'a, U, F> IntoIterator for &'b VecRefWrapperMap<'a, T, U, F>
where
    F: Fn(&'a T) -> U + Clone,
{
    type IntoIter = Map<Iter<'a, T>, F>;
    type Item = U;

    fn into_iter(self) -> Self::IntoIter {
        self.r.iter().map(self.f.clone())
    }
}

// assert_variance!(Container);
