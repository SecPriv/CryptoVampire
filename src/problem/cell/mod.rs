// mod lock;

use crate::{
    assert_variance, asssert_trait,
    container::{allocator::ContainerTools, contained::Containable, reference::Reference},
    formula::{
        formula::ARichFormula,
        function::{
            inner::term_algebra::{cell::Cell, TermAlgebra},
            Function, InnerFunction,
        },
        sort::Sort,
    },
    implderef, implvec,
    utils::{
        precise_as_ref::PreciseAsRef, string_ref::StrRef, traits::RefNamed,
        utils::AlreadyInitialized,
    },
};
use core::fmt::Debug;
use std::sync::Arc;

use super::step::Step;

pub type MemoryCell<'bump> = Reference<'bump, InnerMemoryCell<'bump>>;

// #[derive(Hash, PartialEq, Eq, Clone, Copy)]
// pub struct MemoryCell<'bump> {
//     inner: NonNull<Option<InnerMemoryCell<'bump>>>,
//     container: PhantomData<&'bump ()>,
// }
impl<'bump> Containable<'bump> for InnerMemoryCell<'bump> {}

asssert_trait!(sync_send_cell; InnerMemoryCell; Sync, Send);
assert_variance!(MemoryCell);
unsafe impl<'bump> Sync for MemoryCell<'bump> {}
unsafe impl<'bump> Send for MemoryCell<'bump> {}

// impl<'bump> Ord for MemoryCell<'bump> {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         if self == other {
//             Ordering::Equal
//         } else {
//             self.as_inner()
//                 .cmp(other.as_inner())
//                 .then(self.inner.cmp(&other.inner))
//         }
//     }
// }

// impl<'bump> PartialOrd for MemoryCell<'bump> {
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//         Some(self.cmp(&other))
//     }
// }

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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignement<'bump> {
    pub step: Step<'bump>,
    // pub vars: Vec<Variable>, // those are the step's free variables
    /// all the relevant arguments, this means it doesn't have the last `step` argument
    ///
    /// `args.len() == InnerMemoryCell::args.len()`
    pub args: Arc<[ARichFormula<'bump>]>,
    pub content: ARichFormula<'bump>,
}

impl<'bump> MemoryCell<'bump> {
    /// make a new [MemoryCell] and allocate a [Function] for it
    pub fn new<C>(
        container: &'bump C,
        name: impl Into<String>,
        args: implvec!(Sort<'bump>),
        assignements: implvec!(Assignement<'bump>),
    ) -> Self
    where
        C: ContainerTools<'bump, InnerFunction<'bump>, R<'bump> = Function<'bump>>
            + ContainerTools<'bump, InnerMemoryCell<'bump>, R<'bump> = Self>,
    {
        let (cell, _) = C::alloc_cyclic(container, |(cell, function)| {
            let inner_cell = InnerMemoryCell {
                name: name.into(),
                args: args.into_iter().collect(),
                function: *function,
                assignements: assignements.into_iter().collect(),
            };
            let inner_function = InnerFunction::TermAlgebra(TermAlgebra::Cell(Cell::new(*cell)));
            (inner_cell, inner_function)
        })
        .unwrap();
        cell
    }

    /// not thread safe
    ///
    /// returns an error if `cell` or `function` was already initialized.
    ///
    /// # Safety
    /// This will mutate `cell` and `function` make sure nobody is mutating them
    /// in another thread. Thanks to the check on initialization no one can alias
    /// `cell` or `function` other that with an [C::initialize()] function.
    pub unsafe fn new_with_uninit<C>(
        _container: &'bump C,
        name: impl Into<String>,
        args: implvec!(Sort<'bump>),
        assignements: implvec!(Assignement<'bump>),

        cell: &MemoryCell<'bump>,
        function: &Function<'bump>,
    ) -> Result<(), AlreadyInitialized>
    where
        C: ContainerTools<'bump, InnerFunction<'bump>, R<'bump> = Function<'bump>>
            + ContainerTools<'bump, InnerMemoryCell<'bump>, R<'bump> = Self>,
    {
        let inner_cell = InnerMemoryCell {
            name: name.into(),
            args: args.into_iter().collect(),
            function: *function,
            assignements: assignements.into_iter().collect(),
        };
        let inner_function = InnerFunction::TermAlgebra(TermAlgebra::Cell(Cell::new(*cell)));

        C::initialize(cell, inner_cell)?;
        C::initialize(function, inner_function)?;
        Ok(())
    }

    pub fn name(&self) -> &'bump str {
        &self.precise_as_ref().name
    }

    pub fn args(&self) -> &'bump Vec<Sort<'bump>> {
        &self.precise_as_ref().args
    }

    pub fn function(&self) -> Function<'bump> {
        self.as_inner().function
    }

    pub fn assignements(&self) -> &'bump Vec<Assignement<'bump>> {
        &self.precise_as_ref().assignements
    }
}

impl<'a, 'bump: 'a> RefNamed<'a> for &'a InnerMemoryCell<'bump> {
    fn name_ref(&self) -> StrRef<'a> {
        self.name.as_str().into()
    }
}

// base impl

// impl<'bump> Debug for MemoryCell<'bump> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         self.as_inner().fmt(f)
//     }
// }

// impl<'bump> Reference<'bump> for MemoryCell<'bump> {
//     type Inner<'a> = InnerMemoryCell<'a> where 'a:'bump;

//     fn from_ref(ptr: &'bump Option<InnerMemoryCell<'bump>>) -> Self {
//         Self {
//             inner: NonNull::from(ptr),
//             container: Default::default(),
//         }
//     }

//     fn to_ref(&self) -> &'bump Option<Self::Inner<'bump>> {
//         unsafe { self.inner.as_ref() }
//     }
// }
