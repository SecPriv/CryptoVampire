use std::{cell::RefCell, hash::Hash, sync::Arc};

use itertools::Itertools;

use crate::{
    formula::formula::ARichFormula,
    problem::{cell::MemoryCell, step::Step},
};
use utils::implvec;

use super::{
    call::{CellCall, InputCall, OutGoingCall, StepCall},
    Ancestors, CellOrInput, Dependancy, PreprocessedDependancyGraph,
};
use anyhow::{Ok, Result};
use thiserror::Error;
mod process_functions;

#[derive(Debug, Error)]
pub enum DependancyError {
    #[error("Cell not found")]
    MemoryCellNotFound,
}

/// This is a call graph
///
/// The graph is represented as an adjency list.
///
/// We gathe the cells in an array for later efficiency
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
/// see [CellCall]
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
    Input { step: Step<'bump> },
    CellCall(InnerCellCall<'bump>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum ToNode<'bump> {
    Input(InputCall<'bump>),
    CellCall(InnerCellCall<'bump>),
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

        let pile = RefCell::new(vec![]);
        process_functions::process_steps(&steps, &pile, &cells, &mut input_edges, &mut edges);
        process_functions::process_cell(&steps, &pile, &cells, &mut input_edges, &mut edges);

        let input = InputNode {
            edges_starts: edges.len(),
        };

        for (i, Edges { from, .. }) in edges.iter().enumerate() {
            match from {
                FromNode::CellCall(InnerCellCall { cell_idx: cell, .. }) => {
                    cells[*cell].edges.push(i)
                }
                _ => {}
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
    pub fn ancestors(&self, cell: CellOrInput<'bump>) -> Result<Ancestors<'bump>> {
        let input_idx = self.cells.len();

        // stating position in the `visted` array
        let start_idx = cell
            .into_option()
            .map(|cell| {
                self.cells
                    .iter()
                    .position(|c| c.cell == cell)
                    .ok_or(DependancyError::MemoryCellNotFound)
            })
            .transpose()?
            .unwrap_or(input_idx);

        let mut visited = vec![false; input_idx + 1];
        visited[start_idx] = true;
        let mut todo = vec![start_idx];
        // range of indices of the edges to/from input
        let input_edges = (self.input.edges_starts..self.edges.len()).collect_vec();

        while let Some(next) = todo.pop() {
            visited[next] = true;

            todo.extend(
                self.cells
                    .get(next)
                    .map(|c| c.edges.as_slice())
                    .unwrap_or(input_edges.as_slice()) // if out of bound, it's an input
                    .iter()
                    .map(|ei| &self.edges[*ei])
                    .map(|edge| match edge.to {
                        ToNode::Input(_) => input_idx,
                        ToNode::CellCall(InnerCellCall { cell_idx: cell, .. }) => cell,
                    })
                    .filter(|i| !visited[*i]),
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

impl<'bump> InnerCellCall<'bump> {
    fn as_cell_call(&self, graph: &DependancyGraph<'bump>) -> CellCall<'bump> {
        let InnerCellCall {
            cell_idx: cell,
            timepoint: step,
            args,
        } = self;
        CellCall {
            cell: graph.cells.get(*cell).unwrap().cell,
            timepoint: step.clone(),
            args: args.clone(),
        }
    }
}

impl<'bump> Edges<'bump> {
    fn as_dependancy(&self, graph: &DependancyGraph<'bump>) -> Option<Dependancy<'bump>> {
        match self {
            Edges {
                from: FromNode::Input { .. },
                to: _,
            } => None,

            Edges {
                from: FromNode::CellCall(call),
                to: ToNode::Input(icall),
            } => Some(Dependancy {
                from: call.as_cell_call(graph),
                depends_on: OutGoingCall::Input(icall.clone()),
            }),
            Edges {
                from: FromNode::CellCall(fcall),
                to: ToNode::CellCall(tcall),
            } => Some(Dependancy {
                from: fcall.as_cell_call(graph),
                depends_on: OutGoingCall::Cell(tcall.as_cell_call(graph)),
            }),
        }
    }

    fn from(&self) -> Option<usize> {
        match &self.from {
            FromNode::Input { .. } => None,
            FromNode::CellCall(InnerCellCall { cell_idx: cell, .. }) => Some(*cell),
        }
    }

    fn to(&self) -> Option<usize> {
        match &self.to {
            ToNode::Input(_) => None,
            ToNode::CellCall(InnerCellCall { cell_idx: cell, .. }) => Some(*cell),
        }
    }
}
