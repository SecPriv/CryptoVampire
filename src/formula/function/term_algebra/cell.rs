use std::marker::PhantomData;

use crate::problem::cell::MemoryCell;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Cell<'bump> {
    memory_cell: MemoryCell<'bump>,
}

impl<'bump> Cell<'bump> {
    pub fn memory_cell(&self) -> &MemoryCell<'bump> {
        &self.memory_cell
    }
}
