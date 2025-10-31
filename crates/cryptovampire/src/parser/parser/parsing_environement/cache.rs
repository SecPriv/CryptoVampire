use std::sync::{Arc, Mutex};

use derivative::Derivative;

mod step;
pub use step::StepCache;
use utils::vecref::VecRefClone;

use crate::formula::function::Function;
use crate::formula::function::signature::{FixedRefSignature, Lazy, Signature};
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::{MESSAGE, STEP};
use crate::parser::ast;
use crate::problem::cell::{Assignement, MemoryCell};

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum FunctionCache<'str, 'bump, S> {
    Function(Function<'bump>),
    Step(StepCache<'str, 'bump, S>),
    MemoryCell(CellCache<'str, 'bump, S>),
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, Hash)]
pub struct CellCache<'str, 'bump, S> {
    pub args: Arc<[Sort<'bump>]>,
    pub cell: MemoryCell<'bump>,
    pub function: Function<'bump>,
    pub ast: &'str ast::DeclareCell<'str, S>,
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub assignements: Mutex<Vec<Assignement<'bump>>>,
}

impl<'str, 'bump, S> FunctionCache<'str, 'bump, S> {
    /// to make sure things are still as variant as they should
    #[allow(dead_code)]
    fn shorten_life<'a>(self) -> FunctionCache<'a, 'bump, S>
    where
        'str: 'a,
    {
        self
    }

    /// Returns `true` if the function cache is [`Function`].
    ///
    /// [`Function`]: FunctionCache::Function
    #[must_use]
    #[allow(dead_code)]
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

    #[allow(dead_code)]
    pub fn try_into_function(self) -> Result<Function<'bump>, Self> {
        if let Self::Function(function) = self {
            Ok(function)
        } else {
            Err(self)
        }
    }

    #[allow(dead_code)]
    pub fn as_step_ast(&self) -> Option<&ast::Step<'str, S>> {
        match self {
            Self::Step(StepCache { ast, .. }) => Some(*ast),
            _ => None,
        }
    }

    /// Returns `true` if the function cache is [`Step`].
    ///
    /// [`Step`]: FunctionCache::Step
    #[must_use]
    #[allow(dead_code)]
    pub fn is_step(&self) -> bool {
        matches!(self, Self::Step { .. })
    }

    /// Returns `true` if the function cache is [`MemoryCell`].
    ///
    /// [`MemoryCell`]: FunctionCache::MemoryCell
    #[must_use]
    #[allow(dead_code)]
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
                        .collect::<VecRefClone<'_, _>>(),
                )))
            }
        }
    }

    pub fn as_memory_cell(&self) -> Option<&CellCache<'str, 'bump, S>> {
        if let Self::MemoryCell(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_step(&self) -> Option<&StepCache<'str, 'bump, S>> {
        if let Self::Step(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<'str, 'bump, S> From<Function<'bump>> for FunctionCache<'str, 'bump, S> {
    fn from(value: Function<'bump>) -> Self {
        Self::Function(value)
    }
}
