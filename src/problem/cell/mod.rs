// mod lock;



use crate::{
    assert_variance, asssert_trait,
    container::{
        allocator::ContainerTools,
        reference::{ Reference}, contained::Containable,
    },
    formula::{
        formula::RichFormula,
        function::{
            Function,
        },
        sort::Sort,
    },
    implderef, implvec,
    utils::{
        precise_as_ref::PreciseAsRef, traits::RefNamed, string_ref::StrRef,
    },
};
use core::fmt::Debug;

use super::step::Step;

pub type MemoryCell<'bump> = Reference<'bump, InnerMemoryCell<'bump>>;

// #[derive(Hash, PartialEq, Eq, Clone, Copy)]
// pub struct MemoryCell<'bump> {
//     inner: NonNull<Option<InnerMemoryCell<'bump>>>,
//     container: PhantomData<&'bump ()>,
// }
impl<'bump> Containable<'bump> for InnerMemoryCell<'bump>{}

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
    pub fn new<C>(
        _container: &'bump C,
        _name: implderef!(str),
        _args: implvec!(Sort<'bump>),
        _assignements: implvec!(Assignement<'bump>),
    ) -> Self
    where
        C: ContainerTools<'bump, (Self, Function<'bump>)>,
    {
        // let name = name.to_string();
        // let args = args.into_iter().collect();
        // let assignements = assignements.into_iter().collect();

        // let (_, cell) = unsafe {
        //     Function::new_cyclic(container, |function| {
        //         let inner_content = InnerMemoryCell {
        //             name,
        //             args,
        //             function,
        //             assignements,
        //         };
        //         let inner = container.alloc();
        //         std::ptr::write(inner.as_ptr(), inner_content);
        //         let memory_cell = MemoryCell {
        //             inner,
        //             container: Default::default(),
        //         };
        //         (
        //             InnerFunction::TermAlgebra(TermAlgebra::Cell(Cell::new(memory_cell))),
        //             memory_cell,
        //         )
        //     })
        // };
        // cell
        todo!()
    }

    pub unsafe fn new_with_function<C>(
        _container: &'bump C,
        _old_function: Function<'bump>,
        _name: implderef!(str),
        _args: implvec!(Sort<'bump>),
        _assignements: implvec!(Assignement<'bump>),
    ) -> Self
    where
        C: ContainerTools<'bump, InnerMemoryCell<'bump>>,
    {
        // let name = name.to_string();
        // let args = args.into_iter().collect();
        // let assignements = assignements.into_iter().collect();
        // let cell = {
        //     let inner_content = InnerMemoryCell {
        //         name,
        //         args,
        //         function: old_function,
        //         assignements,
        //     };
        //     let inner = container.alloc();
        //     std::ptr::write(inner.as_ptr(), inner_content);
        //     MemoryCell {
        //         inner,
        //         container: Default::default(),
        //     }
        // };
        // old_function.initiallize(InnerFunction::TermAlgebra(TermAlgebra::Cell(Cell::new(
        //     cell,
        // ))));
        // cell
        todo!()
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

