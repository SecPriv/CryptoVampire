//! The modules with the building and using the [DependancyGraph]

use std::hash::Hash;
use std::sync::Arc;

use itertools::Itertools;
use thiserror::Error;
use utils::implvec;

use super::call::{InputCall, StepCall};
use super::{Ancestors, MacroRef, PreprocessedDependancyGraph};
use crate::error::BaseError;
use crate::formula::formula::ARichFormula;
use crate::problem::cell::MemoryCell;
use crate::problem::step::Step;
mod process_functions;

#[derive(Debug, Error)]
pub enum DependancyError {
    #[error("Cell not found")]
    MemoryCellNotFound,
}

impl From<DependancyError> for BaseError {
    fn from(val: DependancyError) -> Self {
        super::GraphError::from(val).into()
    }
}

/// This is a call graph
///
/// The graph is represented as an adjency list.
///
/// We gather the cells in an array for later efficiency
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct DependancyGraph<'bump> {
    /// the [MemoryCell] in an internal representation
    cells: Vec<GlobNode<'bump>>,
    /// internal representation for the input
    input: InputNode,
    /// edges
    edges: Vec<Edges<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
struct InputNode {
    pub edges_starts: usize,
}

/// A non input node in the graph
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct GlobNode<'bump> {
    pub cell: MemoryCell<'bump>,
    pub edges: Vec<usize>,
}

/// To represent a call to a cell like `cell_idx(args, timepoint)`
///
/// see [FromNode::CellCall] and [ToNode::CellCall]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct InnerCellCall<'bump> {
    /// the index of the cell in [DependancyGraph::cells]
    pub cell_idx: usize,
    /// the time point its calling
    pub timepoint: StepCall<'bump>,
    /// the arguments
    pub args: Arc<[ARichFormula<'bump>]>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct Edges<'bump> {
    pub from: FromNode<'bump>,
    pub to: ToNode<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum FromNode<'bump> {
    Message { step: Step<'bump> },
    Condition { step: Step<'bump> },
    CellCall(InnerCellCall<'bump>),
}

impl<'bump> FromNode<'bump> {
    pub fn message(step: Step<'bump>) -> Self {
        Self::Message { step }
    }
    pub fn condition(step: Step<'bump>) -> Self {
        Self::Condition { step }
    }

    /// Returns `true` if the from node is [`Condition`].
    ///
    /// [`Condition`]: FromNode::Condition
    #[must_use]
    fn is_condition(&self) -> bool {
        matches!(self, Self::Condition { .. })
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum ToNode<'bump> {
    Input(InputCall<'bump>),
    CellCall(InnerCellCall<'bump>),
}

impl<'bump> ToNode<'bump> {
    pub fn get_cell_idx(&self) -> Option<usize> {
        match self {
            ToNode::Input(_) => None,
            ToNode::CellCall(InnerCellCall { cell_idx, .. }) => Some(*cell_idx),
        }
    }
}

impl<'bump> DependancyGraph<'bump> {
    /// Builds a new [DependancyGraph] for a list of steps and cells
    pub fn new(steps: implvec!(Step<'bump>), cells: implvec!(MemoryCell<'bump>)) -> Self {
        let steps = steps.into_iter().collect_vec();
        let mut cells = cells
            .into_iter()
            .map(|cell| GlobNode {
                cell,
                edges: vec![],
            })
            .collect_vec();

        let mut edges = Vec::new();
        let mut input_edges = Vec::new();

        {
            let mut pile = Vec::new();
            process_functions::process_steps(
                &mut pile,
                &steps,
                &cells,
                &mut input_edges,
                &mut edges,
            );
            process_functions::process_cell(
                &mut pile,
                &steps,
                &cells,
                &mut input_edges,
                &mut edges,
            );
        }

        let input = InputNode {
            edges_starts: edges.len(),
        };

        for (i, Edges { from, .. }) in edges.iter().enumerate() {
            if let FromNode::CellCall(InnerCellCall { cell_idx: cell, .. }) = from {
                cells[*cell].edges.push(i)
            }
        }
        edges.extend(input_edges);
        DependancyGraph {
            cells,
            edges,
            input,
        }
    }

    /// From which [MemoryCell] is `cell` called? Is it called by a step?
    ///
    /// set `cell` to [None] to search which [MemoryCell] call an input
    pub fn ancestors(&self, mmacro: MacroRef<'bump>) -> crate::Result<Ancestors<'bump>> {
        let input_idx = self.cells.len();
        let mut visited = vec![false; input_idx + 1];
        let mut to_visit_idx = match mmacro {
            MacroRef::Input => vec![input_idx],
            MacroRef::Cell(cell) => {
                let idx = self
                    .cells
                    .iter()
                    .position(|c| c.cell == cell)
                    .ok_or(DependancyError::MemoryCellNotFound)?;
                vec![idx]
            }
            // get the indices of anything coming from a condition
            MacroRef::Exec => self
                .edges
                .iter()
                .filter(|e| e.from.is_condition())
                .map(|e| e.to.get_cell_idx().unwrap_or(input_idx))
                .collect(),
        };

        let input_edges = (self.input.edges_starts..self.edges.len()).collect_vec();

        while let Some(next) = to_visit_idx.pop() {
            if visited[next] {
                continue;
            }

            visited[next] = true;

            to_visit_idx.extend(
                self.cells
                    .get(next)
                    .map(|c| c.edges.as_slice())
                    .unwrap_or(input_edges.as_slice()) // if out of bound, it's an input
                    .iter()
                    .map(|ei| &self.edges[*ei])
                    .map(|edge| edge.to.get_cell_idx().unwrap_or(input_idx)), // .filter(|i| !visited[*i]),
            )
        }

        let input = visited.pop().unwrap();
        Ok(Ancestors {
            input,
            cells: visited
                .into_iter()
                .enumerate()
                .filter(|(_, b)| *b)
                .map(|(i, _)| self.cells[i].cell)
                .collect(),
        })
    }

    /// Preprocess the graph
    pub fn preprocess(&self) -> PreprocessedDependancyGraph<'bump> {
        self.into()
    }

    /// The cells in the graph
    pub fn cells<'a>(&'a self) -> impl Iterator<Item = MemoryCell<'bump>> + 'a {
        self.cells.iter().map(|GlobNode { cell, .. }| *cell)
    }
}
