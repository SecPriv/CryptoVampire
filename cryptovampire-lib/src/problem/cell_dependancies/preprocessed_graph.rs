use hashbrown::HashMap;
use itertools::Itertools;
use utils::implvec;

use crate::problem::{cell::MemoryCell, step::Step};

use super::{Ancestors, CellOrInput, DependancyGraph};

/// Preprocess all the information currently retrivable from a [DependancyGraph]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PreprocessedDependancyGraph<'bump> {
    input: Ancestors<'bump>,
    cells: HashMap<MemoryCell<'bump>, Ancestors<'bump>>,
}

impl<'bump> PreprocessedDependancyGraph<'bump> {
    pub fn new(steps: implvec!(Step<'bump>), cells: implvec!(MemoryCell<'bump>)) -> Self {
        DependancyGraph::new(steps, cells).into()
    }

    /// the [Ancestors] of the input
    pub fn input(&self) -> &Ancestors<'bump> {
        &self.input
    }

    /// the [Ancestors] of the cells
    pub fn cells(&self) -> &HashMap<MemoryCell<'bump>, Ancestors<'bump>> {
        &self.cells
    }

    /// Get the ancestor (if it exists) of a [MemoryCell] or an input
    pub fn ancestors(&self, arg: CellOrInput<'bump>) -> Option<&Ancestors<'bump>> {
        match arg {
            CellOrInput::Input => Some(self.input()),
            CellOrInput::Cell(c) => self.cells().get(&c),
        }
    }
}

impl<'bump, 'a> From<&'a DependancyGraph<'bump>> for PreprocessedDependancyGraph<'bump> {
    fn from(depgraph: &'a DependancyGraph<'bump>) -> Self {
        let cells = depgraph
            .cells()
            .map(|c| depgraph.ancestors(CellOrInput::Cell(c)).map(|a| (c, a)))
            .try_collect()
            .unwrap();
        let input = depgraph.ancestors(CellOrInput::Input).unwrap();
        // the unwrap shouldn't fails because the cells are part of `depgraph`
        Self { input, cells }
    }
}

impl<'bump> From<DependancyGraph<'bump>> for PreprocessedDependancyGraph<'bump> {
    fn from(depgraph: DependancyGraph<'bump>) -> Self {
        (&depgraph).into()
    }
}
