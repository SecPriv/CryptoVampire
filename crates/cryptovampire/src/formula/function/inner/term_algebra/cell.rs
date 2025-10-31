use crate::formula::function::Function;
use crate::formula::function::signature::FixedRefSignature;
use crate::formula::function::traits::{FixedSignature, MaybeEvaluatable};
use crate::formula::sort::builtins::{MESSAGE, STEP};
use crate::problem::cell::MemoryCell;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Cell<'bump> {
    memory_cell: MemoryCell<'bump>,
}

impl<'bump> Cell<'bump> {
    pub fn new(memory_cell: MemoryCell<'bump>) -> Self {
        Self { memory_cell }
    }

    pub fn memory_cell(&self) -> MemoryCell<'bump> {
        self.memory_cell
    }

    pub fn name(&self) -> &str {
        self.memory_cell.name()
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Cell<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        None
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Cell<'bump> {
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        FixedRefSignature {
            out: MESSAGE.as_sort(),
            args: self
                .memory_cell()
                .args()
                .iter()
                .cloned()
                .chain([STEP.as_sort()])
                .collect(),
        }
    }
}
