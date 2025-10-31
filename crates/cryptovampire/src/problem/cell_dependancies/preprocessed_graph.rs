use hashbrown::HashMap;
use itertools::Itertools;
use utils::implvec;

use super::{Ancestors, DependancyGraph, MacroRef};
use crate::problem::cell::MemoryCell;
use crate::problem::step::Step;

/// Preprocess all the information currently retrivable from a [DependancyGraph]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PreprocessedDependancyGraph<'bump> {
    input: Ancestors<'bump>,
    exec: Ancestors<'bump>,
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
    pub fn ancestors(&self, arg: MacroRef<'bump>) -> Option<&Ancestors<'bump>> {
        match arg {
            MacroRef::Exec => Some(self.exec()),
            MacroRef::Input => Some(self.input()),
            MacroRef::Cell(c) => self.cells().get(&c),
        }
    }

    pub fn exec(&self) -> &Ancestors<'bump> {
        &self.exec
    }
}

impl<'bump, 'a> From<&'a DependancyGraph<'bump>> for PreprocessedDependancyGraph<'bump> {
    fn from(depgraph: &'a DependancyGraph<'bump>) -> Self {
        let cells = depgraph
            .cells()
            .map(|c| depgraph.ancestors(MacroRef::Cell(c)).map(|a| (c, a)))
            .try_collect()
            .unwrap();
        let input = depgraph.ancestors(MacroRef::Input).unwrap();
        let exec = depgraph.ancestors(MacroRef::Exec).unwrap();
        // the unwrap shouldn't fails because the cells are part of `depgraph`
        Self { input, cells, exec }
    }
}

impl<'bump> From<DependancyGraph<'bump>> for PreprocessedDependancyGraph<'bump> {
    fn from(depgraph: DependancyGraph<'bump>) -> Self {
        (&depgraph).into()
    }
}
