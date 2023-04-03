mod lock;

use std::{
    cell::UnsafeCell,
    marker::PhantomData,
    num::NonZeroUsize,
    ptr::NonNull,
    rc::Rc,
    sync::atomic::{self, AtomicUsize},
};

use crate::{
    container::{CanBeAllocated, Container},
    formula::{
        // builtins::types::{MSG_NAME, STEP_NAME},
        formula::RichFormula,
        function::Function,
        sort::Sort,
    },
};
use core::fmt::Debug;

use self::lock::{IsLock, Lock, LockError};

use super::step::Step;

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
pub struct MemoryCell<'bump> {
    inner: NonNull<InnerMemoryCell<'bump>>,
    container: PhantomData<&'bump ()>,
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
    assignements: UnsafeCell<Vec<Assignement<'bump>>>,
    lock: IsLock,
}

impl<'bump> InnerMemoryCell<'bump> {
    pub(crate) fn assignements(&self) -> Result<&Vec<Assignement<'bump>>, LockError> {
        match &self.lock.is_free() {
            true => unsafe { self.assignements.get().as_ref() }.ok_or(LockError::NullPointer), // note: will never return None
            _ => Err(LockError::WrongLock),
        }
    }

    pub(crate) fn get_assignement(
        &self,
        lock: &Lock,
    ) -> Result<&Vec<Assignement<'bump>>, LockError> {
        if lock.is_correspinding_lock(&self.lock) {
            unsafe { self.assignements.get().as_ref() }.ok_or(LockError::NullPointer)
        } else {
            Err(LockError::WrongLock)
        }
    }

    pub(crate) fn get_assignement_mut(
        &self,
        lock: &mut Lock,
    ) -> Result<&mut Vec<Assignement<'bump>>, LockError> {
        if lock.is_correspinding_lock(&self.lock) {
            unsafe { self.assignements.get().as_mut() }.ok_or(LockError::NullPointer)
        } else {
            Err(LockError::WrongLock)
        }
    }

    pub(crate) fn freeze(&self, lock: Lock) -> Result<(), LockError> {
        if lock.is_correspinding_lock(&self.lock) {
            self.lock.freeze();
            Ok(())
        } else {
            Err(LockError::WrongLock)
        }
    }
}

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
    pub fn name(&self) -> &str {
        &self.as_ref().name
    }

    pub fn args(&self) -> &Vec<Sort> {
        &self.as_ref().args
    }

    pub fn function(&self) -> &Function {
        &self.as_ref().function
    }

    pub fn assignements(&self) -> Result<&Vec<Assignement>, LockError> {
        match &self.as_ref().lock.is_free() {
            true => {
                unsafe { self.as_ref().assignements.get().as_ref() }.ok_or(LockError::NullPointer)
            } // note: will never return None
            _ => Err(LockError::WrongLock),
        }
    }

    pub fn add_assignement(
        &self,
        lock: &mut Lock,
        assignement: Assignement<'bump>,
    ) -> Result<(), LockError> {
        self.as_ref().get_assignement_mut(lock)?.push(assignement);
        Ok(())
    }

    pub fn new(container: &Container<'bump>, name: String, args: Vec<Sort<'bump>>) -> Self {
        let inner = InnerMemoryCell {
            name,
            args,
            function: todo!(),
            assignements: UnsafeCell::default(),
            lock: IsLock::new(),
        };
        Self::allocate(container, inner)
    }
}

impl<'bump> AsRef<InnerMemoryCell<'bump>> for MemoryCell<'bump> {
    fn as_ref(&self) -> &InnerMemoryCell<'bump> {
        unsafe { self.inner.as_ref() } // same as always
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
        A: crate::container::ScopeAllocator<Self::Inner> + 'bump,
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
