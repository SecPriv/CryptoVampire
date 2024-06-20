//! This file help to solve searching though the dependency graph of memorycells
//!  and inputs looking for subterm
use std::sync::Arc;

use crate::formula::{formula::ARichFormula, function::inner::term_algebra::input::Input};

use super::{cell::MemoryCell, step::Step};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Dependancy<'bump> {
    pub from: call::CellCall<'bump>,
    pub depends_on: call::OutGoingCall<'bump>,
}

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

/// The graph itself

fn some_iter<T, I: IntoIterator<Item = T>>(iter: Option<I>) -> impl Iterator<Item = T> {
    enum PossiblyEmptyIterator<T, I: IntoIterator<Item = T>> {
        Empty,
        Contains(<I as IntoIterator>::IntoIter),
    }

    impl<T, I: IntoIterator<Item = T>> Iterator for PossiblyEmptyIterator<T, I> {
        type Item = T;

        fn next(&mut self) -> Option<Self::Item> {
            match self {
                PossiblyEmptyIterator::Empty => None,
                PossiblyEmptyIterator::Contains(i) => i.next(),
            }
        }
    }

    match iter {
        Some(i) => PossiblyEmptyIterator::<T, I>::Contains(i.into_iter()),
        None => PossiblyEmptyIterator::Empty,
    }
}
