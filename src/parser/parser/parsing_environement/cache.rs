use std::sync::{Arc, Mutex};

use derivative::Derivative;

use crate::{
    formula::{
        function::{
            signature::{FixedRefSignature, Lazy, Signature},
            Function,
        },
        sort::{
            builtins::{MESSAGE, STEP},
            Sort,
        },
    },
    parser::ast,
    problem::{
        cell::{Assignement, MemoryCell},
        step::Step,
    },
    utils::vecref::VecRefClone,
};

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum FunctionCache<'str, 'bump> {
    Function(Function<'bump>),
    Step(StepCache<'str, 'bump>),
    MemoryCell(CellCache<'str, 'bump>),
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct StepCache<'str, 'bump> {
    pub args: Arc<[Sort<'bump>]>,
    pub args_name: Arc<[&'str str]>,
    pub ast: &'str ast::Step<'str>,
    pub function: Function<'bump>,
    pub step: Step<'bump>,
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, Hash)]
pub struct CellCache<'str, 'bump> {
    pub args: Arc<[Sort<'bump>]>,
    pub cell: MemoryCell<'bump>,
    pub function: Function<'bump>,
    pub ast : &'str ast::DeclareCell<'str>,
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub assignements: Mutex<Vec<Assignement<'bump>>>,
}

impl<'str, 'bump> FunctionCache<'str, 'bump> {
    /// Returns `true` if the function cache is [`Function`].
    ///
    /// [`Function`]: FunctionCache::Function
    #[must_use]
    pub fn is_function(&self) -> bool {
        matches!(self, Self::Function { .. })
    }

    pub fn as_function(&self) -> Option<&Function<'bump>> {
        if let Self::Function(function) = self {
            Some(function)
        } else {
            None
        }
    }

    pub fn try_into_function(self) -> Result<Function<'bump>, Self> {
        if let Self::Function(function) = self {
            Ok(function)
        } else {
            Err(self)
        }
    }

    pub fn as_step_ast(&self) -> Option<&ast::Step<'str>> {
        match self {
            Self::Step(StepCache { ast, .. }) => Some(ast),
            _ => None,
        }
    }

    /// Returns `true` if the function cache is [`Step`].
    ///
    /// [`Step`]: FunctionCache::Step
    #[must_use]
    pub fn is_step(&self) -> bool {
        matches!(self, Self::Step { .. })
    }

    /// Returns `true` if the function cache is [`MemoryCell`].
    ///
    /// [`MemoryCell`]: FunctionCache::MemoryCell
    #[must_use]
    pub fn is_memory_cell(&self) -> bool {
        matches!(self, Self::MemoryCell { .. })
    }

    pub fn get_function(&self) -> Function<'bump> {
        match self {
            FunctionCache::Function(function)
            | FunctionCache::Step(StepCache { function, .. })
            | FunctionCache::MemoryCell(CellCache { function, .. }) => *function,
        }
    }

    pub fn signature(&self) -> impl Signature<'bump> + '_ {
        match self {
            FunctionCache::Function(function) => Lazy::A(function.signature()),
            FunctionCache::Step(StepCache { args, .. }) => Lazy::B(Lazy::A(
                FixedRefSignature::new(STEP.as_sort(), args.clone()),
            )),
            FunctionCache::MemoryCell(CellCache { args, .. }) => {
                Lazy::B(Lazy::B(FixedRefSignature::new(
                    MESSAGE.as_sort(),
                    args.iter()
                        .cloned()
                        .chain([STEP.as_sort()])
                        .collect::<VecRefClone<_>>(),
                )))
            }
        }
    }

    pub fn enforce_variance<'str2, 'bump2>(&self) -> &FunctionCache<'str2, 'bump2>
    where
        'str: 'str2,
        'bump: 'bump2,
    {
        assert!(self.is_function() || self.is_step());
        unsafe { std::mem::transmute(&self) } // only MemoryCell is invariant
    }

    pub fn as_memory_cell(&self) -> Option<&CellCache<'str, 'bump>> {
        if let Self::MemoryCell(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<'str, 'bump> From<Function<'bump>> for FunctionCache<'str, 'bump> {
    fn from(value: Function<'bump>) -> Self {
        Self::Function(value)
    }
}
