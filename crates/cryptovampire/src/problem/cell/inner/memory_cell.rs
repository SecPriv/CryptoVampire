use utils::precise_as_ref::PreciseAsRef;
use utils::utils::AlreadyInitialized;
use utils::{assert_variance, implvec};

use super::{Assignement, InnerMemoryCell};
use crate::container::allocator::ContainerTools;
use crate::container::reference::Reference;
use crate::formula::function::inner::term_algebra::TermAlgebra;
use crate::formula::function::inner::term_algebra::cell::Cell;
use crate::formula::function::{Function, InnerFunction};
use crate::formula::sort::Sort;

pub type MemoryCell<'bump> = Reference<'bump, InnerMemoryCell<'bump>>;

assert_variance!(MemoryCell);
// unsafe impl<'bump> Sync for MemoryCell<'bump> {}
// unsafe impl<'bump> Send for MemoryCell<'bump> {}

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
        self.precise_as_ref().name()
    }

    pub fn args(&self) -> &'bump [Sort<'bump>] {
        self.precise_as_ref().args()
    }

    pub fn function(&self) -> Function<'bump> {
        self.as_ref().function()
    }

    pub fn assignements(&self) -> &'bump [Assignement<'bump>] {
        &self.precise_as_ref().assignements
    }
}
