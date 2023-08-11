use std::sync::Arc;

use crate::{
    formula::{
        function::{
            signature::{AsFixedSignature, FixedRefSignature, Lazy, Signature},
            Function,
        },
        sort::{
            builtins::{MESSAGE, STEP},
            Sort,
        },
    },
    parser::ast,
    problem::{cell::{MemoryCell, Assignement}, step::Step},
    utils::{arc_into_iter::ArcIntoIter, vecref::VecRefClone},
};

#[derive(Hash, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum FunctionCache<'str, 'bump> {
    Function {
        function: Function<'bump>,
    },
    Step {
        args: Arc<[Sort<'bump>]>,
        args_name: Arc<[&'str str]>,
        ast: Box<ast::Step<'str>>,
        function: Function<'bump>,
        step: Step<'bump>,
    },
    MemoryCell {
        args: Arc<[Sort<'bump>]>,
        cell: MemoryCell<'bump>,
        function: Function<'bump>,
        assignements: Vec<Assignement<'bump>>
    },
}

#[derive(Hash, Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct MSignature<'str, 'bump> {
    names: Box<[&'str str]>,
    sorts: Arc<[Sort<'bump>]>,
}

impl<'str, 'bump> MSignature<'str, 'bump> {
    pub fn new(names: Box<[&'str str]>, sorts: Arc<[Sort<'bump>]>) -> Self {
        Self { names, sorts }
    }
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
        if let Self::Function { function } = self {
            Some(function)
        } else {
            None
        }
    }

    pub fn try_into_function(self) -> Result<Function<'bump>, Self> {
        if let Self::Function { function } = self {
            Ok(function)
        } else {
            Err(self)
        }
    }

    pub fn as_step_ast(&self) -> Option<&ast::Step<'str>> {
        match self {
            Self::Step { ast, .. } => Some(ast),
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
            FunctionCache::Function { function }
            | FunctionCache::Step { function, .. }
            | FunctionCache::MemoryCell { function, .. } => *function,
        }
    }

    pub fn signature(&self) -> impl Signature<'bump> + '_ {
        match self {
            FunctionCache::Function { function } => Lazy::A(function.signature()),
            FunctionCache::Step { args, .. } => Lazy::B(Lazy::A(FixedRefSignature::new(
                STEP.as_sort(),
                args.clone(),
            ))),
            FunctionCache::MemoryCell { args, .. } => {
                Lazy::B(Lazy::B(FixedRefSignature::new(
                    MESSAGE.as_sort(),
                    args
                        .iter()
                        .cloned()
                        .chain([STEP.as_sort()])
                        .collect::<VecRefClone<_>>(),
                )))
            }
        }
    }
}

impl<'str, 'bump> From<Function<'bump>> for FunctionCache<'str, 'bump> {
    fn from(value: Function<'bump>) -> Self {
        Self::Function { function: value }
    }
}
