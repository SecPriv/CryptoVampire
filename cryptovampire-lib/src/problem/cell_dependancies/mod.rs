//! This module help to solve searching though the dependency graph of memorycells
//!  and inputs looking for subterm

use super::{cell::MemoryCell, step::Step};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DependancyFromStep<'bump> {
    pub steps_origin: Vec<Step<'bump>>,
    pub cell: Option<MemoryCell<'bump>>,
}

mod call;
mod cell_or_input;
mod graph;
mod preprocessed_graph;
pub use cell_or_input::CellOrInput;
pub use graph::DependancyGraph;
pub use preprocessed_graph::PreprocessedDependancyGraph;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Ancestors<'bump> {
    pub input: bool,
    pub cells: Vec<MemoryCell<'bump>>,
}
