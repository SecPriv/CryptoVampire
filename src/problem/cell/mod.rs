// mod lock;

use std::{
    cmp::Ordering,
    marker::PhantomData,
    ptr::NonNull,
};

use crate::{
    container::{CanBeAllocated},
    formula::{
        // builtins::types::{MSG_NAME, STEP_NAME},
        formula::RichFormula,
        function::Function,
        sort::Sort,
    },
    utils::precise_as_ref::PreciseAsRef,
};
use core::fmt::Debug;

use super::step::Step;

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
pub struct MemoryCell<'bump> {
    inner: NonNull<InnerMemoryCell<'bump>>,
    container: PhantomData<&'bump ()>,
}

impl<'bump> Ord for MemoryCell<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            Ordering::Equal
        } else {
            self.as_ref()
                .cmp(other.as_ref())
                .then(self.inner.cmp(&other.inner))
        }
    }
}

impl<'bump> PartialOrd for MemoryCell<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}

// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
// pub struct PreMemoryCell<'bump>(Box<InnerMemoryCell<'bump>>);

#[derive(Debug)]
pub struct InnerMemoryCell<'bump> {
    name: String,
    /// the arguments of the cell
    args: Vec<Sort<'bump>>,
    /// the function used to refer to it
    ///
    /// NB: this function takes one more argument of sort step
    function: Function<'bump>,
    /// is accessible iff lock is `Immutable` or using the right lock
    pub assignements: Vec<Assignement<'bump>>,
}

impl<'bump> Eq for InnerMemoryCell<'bump> {}
impl<'bump> PartialEq for InnerMemoryCell<'bump> {
    fn eq(&self, other: &Self) -> bool {
        self.function == other.function && self.name == other.name && self.args == other.args
    }
}
impl<'bump> PartialOrd for InnerMemoryCell<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<'bump> Ord for InnerMemoryCell<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name
            .cmp(&other.name)
            .then(self.function.cmp(&other.function))
            .then(self.args.cmp(&other.args))
    }
}
impl<'bump> std::hash::Hash for InnerMemoryCell<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.args.hash(state);
        self.function.hash(state);
    }
}

impl<'bump> InnerMemoryCell<'bump> {}

unsafe impl<'bump> Sync for InnerMemoryCell<'bump> {}
unsafe impl<'bump> Send for InnerMemoryCell<'bump> {}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Assignement<'bump> {
    pub step: Step<'bump>,
    // pub vars: Vec<Variable>, // those are the step's free variables
    /// all the relevant arguments, this means it doesn't have the last `step` argument
    ///
    /// `args.len() == InnerMemoryCell::args.len()`
    pub args: Vec<RichFormula<'bump>>,
    pub content: RichFormula<'bump>,
}

impl<'bump> MemoryCell<'bump> {
    pub fn name(&self) -> &'bump str {
        &self.precise_as_ref().name
    }

    pub fn args(&self) -> &'bump Vec<Sort> {
        &self.precise_as_ref().args
    }

    pub fn function(&self) -> Function {
        self.as_ref().function
    }

    pub fn assignements(&self) -> &'bump Vec<Assignement<'bump>> {
        &self.precise_as_ref().assignements
    }
}

impl<'bump> PreciseAsRef<'bump, InnerMemoryCell<'bump>> for MemoryCell<'bump> {
    fn precise_as_ref(&self) -> &'bump InnerMemoryCell<'bump> {
        unsafe { self.inner.as_ref() } // same as always
    }
}

impl<'bump> AsRef<InnerMemoryCell<'bump>> for MemoryCell<'bump> {
    fn as_ref(&self) -> &InnerMemoryCell<'bump> {
        self.precise_as_ref()
    }
}

// base impl

impl<'bump> Debug for MemoryCell<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl<'bump> CanBeAllocated<'bump> for MemoryCell<'bump> {
    type Inner = InnerMemoryCell<'bump>;

    fn allocate<A>(allocator: &'bump A, inner: Self::Inner) -> Self
    where
        A: crate::container::ScopeAllocator<'bump, Self::Inner> + 'bump,
    {
        let inner = unsafe {
            let ptr = allocator.alloc();
            ptr.as_ptr().write(inner);
            ptr
        };
        MemoryCell {
            inner,
            container: Default::default(),
        }
    }
}
