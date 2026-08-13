//! This module help to solve searching though the dependency graph of memorycells
//!  and inputs looking for subterm

use super::cell::MemoryCell;

mod call;
mod graph;
mod macro_ref;
mod preprocessed_graph;
pub use graph::DependancyGraph;
pub use macro_ref::MacroRef;
pub use preprocessed_graph::PreprocessedDependancyGraph;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Ancestors<'bump> {
    pub input: bool,
    pub cells: Vec<MemoryCell<'bump>>,
}

#[derive(Debug, thiserror::Error)]
pub enum GraphError {
    #[error(transparent)]
    DependancyError(#[from] graph::DependancyError),
}
