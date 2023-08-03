use std::{cell::RefCell, ptr::NonNull};

use crate::{formula::{sort::InnerSort, function::InnerFunction}, problem::{step::InnerStep, cell::InnerMemoryCell}};



type InnerContainer<T> = RefCell<Vec<NonNull<T>>>;

pub struct ScopedContainer<'bump> {
    sorts: InnerContainer<InnerSort<'bump>>,
    functions: InnerContainer<InnerFunction<'bump>>,
    steps: InnerContainer<InnerStep<'bump>>,
    cells: InnerContainer<InnerMemoryCell<'bump>>,
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

impl<'bump> ScopedContainer<'bump> {
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
        fn shorten_life<'a, 'short, 'long>(x: &'a mut ScopedContainer<'long>) -> &'a mut ScopedContainer<'short>
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