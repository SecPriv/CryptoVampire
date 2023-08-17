use std::sync::Arc;

use crate::formula::formula::ARichFormula;

use super::{cell::MemoryCell, step::Step};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Dependancy<'bump> {
    pub from: CellCall<'bump>,
    pub depends_on: OutGoingCall<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DependancyFromStep<'bump> {
    pub steps_origin: Vec<Step<'bump>>,
    pub cell: Option<MemoryCell<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum OutGoingCall<'bump> {
    Input(InputCall<'bump>),
    Cell(CellCall<'bump>),
}

/// call `cell(args, step)`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CellCall<'bump> {
    pub cell: MemoryCell<'bump>,
    pub timepoint: StepCall<'bump>,
    pub args: Arc<[ARichFormula<'bump>]>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InputCall<'bump> {
    pub step: StepCall<'bump>,
    // pub args: &'pbl [RichFormula],
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum StepCall<'bump> {
    Step(Step<'bump>),
    General(ARichFormula<'bump>),
}

pub mod graph {

    use std::{cell::RefCell, convert::identity, sync::Arc};

    use itertools::Itertools;

    use crate::{
        formula::{
            formula::{ARichFormula, RichFormula},
            function::{inner::term_algebra::TermAlgebra, InnerFunction},
            sort::builtins::STEP,
            utils::formula_iterator::{FormulaIterator, IteratorFlags},
            variable::Variable,
        },
        implvec,
        problem::{
            cell::{Assignement, MemoryCell},
            step::Step,
        },
        utils::{arc_into_iter::ArcIntoIter, utils::repeat_n_zip},
    };

    use super::{CellCall, Dependancy, DependancyFromStep, InputCall, OutGoingCall, StepCall};
    use anyhow::{Ok, Result};
    use thiserror::Error;

    /// This is a call graph
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
        /// the index of the cell
        pub cell_idx: usize,
        /// the time point its calling
        pub timepoint: StepCall<'bump>,
        /// the argument
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

    //  impl<'pbl> From<&'pbl Problem> for DependancyGraph<'pbl> {
    // }

    #[derive(Debug, Error)]
    pub enum DependancyError {
        #[error("Cell not found")]
        MemoryCellNotFound,
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
    pub struct Ancestors<'bump> {
        pub input: bool,
        pub cells: Vec<MemoryCell<'bump>>,
    }

    impl<'bump> DependancyGraph<'bump> {
        pub fn new(steps: implvec!(Step<'bump>), cells: implvec!(MemoryCell<'bump>)) -> Self {
            let steps = steps.into_iter().collect_vec();
            let mut cells = cells
                .into_iter()
                .map(|cell| GlobNode {
                    cell,
                    edges: vec![],
                })
                .collect_vec();
            // let just_cells = cells
            //     .iter()
            //     .map(|GlobNode { cell, .. }| *cell)
            //     .collect_vec();
            let mut edges = Vec::new();
            let mut input_edges = Vec::new();

            let pile = RefCell::new(vec![]);
            process_steps(&steps, &pile, &cells, &mut input_edges, &mut edges);
            process_cell(&steps, &pile, &cells, &mut input_edges, &mut edges);

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
        pub fn ancestors(&self, cell: Option<MemoryCell<'bump>>) -> Result<Ancestors<'bump>> {
            let input_idx = self.cells.len();

            // stating position in the `visted` array
            let start_idx = cell
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

        /// use None for input
        pub fn find_dependencies(
            &self,
            cell: Option<MemoryCell<'bump>>,
        ) -> Result<Vec<Dependancy<'bump>>> {
            let cell = cell
                .map(|cell| {
                    self.cells
                        .iter()
                        .position(|c| &c.cell == &cell)
                        .ok_or(DependancyError::MemoryCellNotFound)
                })
                .transpose()?;

            Ok(self.inner_find_dependencies(cell))
        }

        fn inner_find_dependencies(&self, cell: Option<usize>) -> Vec<Dependancy<'bump>> {
            let mut not_visited_edge = vec![true; self.edges.len()];
            let mut not_visited_node = vec![true; self.cells.len()];
            let mut todo = vec![cell];
            let mut result = vec![];

            let mut not_visited_input = true;

            while let Some(cell) = todo.pop() {
                match cell {
                    Some(cell) => not_visited_node[cell] = false,
                    None => not_visited_input = false,
                }

                let deps = match cell {
                    Some(cell) => self.cells[cell]
                        .edges
                        .iter()
                        .cloned()
                        .filter(|i| not_visited_edge[*i])
                        .collect_vec(),
                    None => (self.input.edges_starts..self.edges.len())
                        .filter(|i| not_visited_edge[*i])
                        .collect_vec(),
                };

                result.extend(deps.iter().flat_map(|&i| self.edges[i].as_dependancy(self)));

                todo.extend(deps.iter().filter_map(|&i| {
                    not_visited_edge[i] = false;
                    match &self.edges[i].to {
                        ToNode::Input(_) if not_visited_input => Some(None),
                        ToNode::CellCall(InnerCellCall { cell_idx: cell, .. })
                            if not_visited_node[*cell] =>
                        {
                            Some(Some(*cell))
                        }
                        _ => None,
                    }
                }))
            }
            result
        }

        pub fn find_dependencies_keep_steps(
            &self,
            cell: MemoryCell<'bump>,
        ) -> Result<Vec<DependancyFromStep<'bump>>> {
            let cell = self
                .cells
                .iter()
                .position(|c| &c.cell == &cell)
                .ok_or(DependancyError::MemoryCellNotFound)?;

            let per_step_dep = self.cells[cell]
                .edges
                .iter()
                .map(|i| {
                    let (i, d, s) = if let Edges {
                        from:
                            FromNode::CellCall(InnerCellCall {
                                cell_idx: c,
                                timepoint: StepCall::Step(s),
                                ..
                            }),
                        to,
                    } = &self.edges[*i]
                    {
                        assert_eq!(*c, cell);
                        match to {
                            ToNode::Input(_) => (None, self.inner_find_dependencies(None), s),
                            ToNode::CellCall(InnerCellCall { cell_idx: cell, .. }) => {
                                (Some(*cell), self.inner_find_dependencies(Some(*cell)), s)
                            }
                        }
                    } else {
                        unreachable!()
                    };

                    let d = d
                        .into_iter()
                        .map(|Dependancy { depends_on, .. }| match depends_on {
                            OutGoingCall::Input(_) => None,
                            OutGoingCall::Cell(CellCall { cell, .. }) => Some(cell),
                        })
                        .chain([i.map(|i| self.cells[i].cell)].into_iter())
                        .unique()
                        .collect_vec();
                    (d, s)
                })
                .flat_map(|(d, s)| d.into_iter().map(move |om| (s, om)));

            let mut result = vec![];

            for (s, om) in per_step_dep.into_iter() {
                let dfs = result
                    .iter()
                    .position(|dfs: &DependancyFromStep| dfs.cell == om)
                    .unwrap_or_else(|| {
                        let i = result.len();
                        result.push(DependancyFromStep {
                            steps_origin: vec![],
                            cell: om,
                        });
                        i
                    });
                if !result[dfs].steps_origin.contains(s) {
                    result[dfs].steps_origin.push(*s)
                }
            }

            Ok(result)
        }

        pub fn find_dependencies_from_step(&self, step: Step<'bump>) -> Vec<MemoryCell<'bump>> {
            let mut not_visited = vec![true; self.cells.len()];
            let mut not_visited_input = true;

            let mut todo = self.edges[self.input.edges_starts..]
                .iter()
                .filter_map(|e| match e {
                    Edges {
                        from: FromNode::Input { step: s },
                        ..
                    } if *s == step => Some(e.to()),
                    _ => None,
                })
                .unique()
                .collect_vec();

            std::iter::from_fn(move || match todo.pop() {
                Some(Some(i)) => {
                    not_visited[i] = false;
                    let gn = &self.cells[i];
                    todo.extend(gn.edges.iter().map(|e| self.edges[*e].to()).filter(
                        |to| match to {
                            Some(i) => not_visited[*i],
                            None => not_visited_input,
                        },
                    ));

                    Some(Some(gn.cell))
                }
                Some(None) => {
                    not_visited_input = false;
                    todo.extend(
                        self.edges[self.input.edges_starts..]
                            .iter()
                            .map(|e| e.to())
                            .filter(|to| match to {
                                Some(i) => not_visited[*i],
                                None => not_visited_input,
                            }),
                    );
                    Some(None)
                }
                _ => None,
            })
            .filter_map(identity)
            .collect_vec()
        }
    }

    fn process_steps<'bump>(
        steps: &Vec<Step<'bump>>,
        pile: &RefCell<Vec<((), ARichFormula<'bump>)>>,
        cells: &Vec<GlobNode<'bump>>,
        input_edges: &mut Vec<Edges<'bump>>,
        edges: &mut Vec<Edges<'bump>>,
    ) {
        for step in steps {
            let from = FromNode::Input { step: *step };
            let _step_call = StepCall::Step(*step);
            let mut pile = pile.borrow_mut();
            pile.clear();
            pile.extend([step.message_arc(), step.condition_arc()].map(|x| ((), x.shallow_copy())));

            let iter = FormulaIterator {
                pile,
                passed_along: Some(()),
                flags: IteratorFlags::QUANTIFIER,
                f: |_, f: ARichFormula<'bump>| match f.as_ref() {
                    RichFormula::Var(Variable { sort, .. }) if sort == &STEP.as_sort() => {
                        panic!("time point variable are not allowed in protocol")
                    }
                    RichFormula::Fun(fun, args) => match fun.as_inner() {
                        InnerFunction::TermAlgebra(TermAlgebra::Cell(c)) => {
                            let c = c.memory_cell();
                            let cell_idx = cells.iter().position(|g| g.cell == c).unwrap();
                            let to_node = ToNode::CellCall(InnerCellCall {
                                cell_idx,
                                timepoint: StepCall::General(args.last().unwrap().shallow_copy()),
                                args: args[..args.len() - 1].iter().cloned().collect(),
                            });
                            (Some(to_node), repeat_n_zip((), [].into()))
                        }
                        InnerFunction::Step(_s) => {
                            let to_node = ToNode::Input(InputCall {
                                step: StepCall::General(f),
                            });
                            (Some(to_node), repeat_n_zip((), [].into()))
                        }
                        _ => (None, repeat_n_zip((), ArcIntoIter::from(args))),
                    },
                    _ => (None, repeat_n_zip((), [].into())),
                },
            };

            iter.for_each(|to_node| match &to_node {
                ToNode::Input(_) => input_edges.push(Edges {
                    from: from.clone(),
                    to: to_node,
                }),
                ToNode::CellCall(_) => edges.push(Edges {
                    from: from.clone(),
                    to: to_node,
                }),
            })
        }
    }

    fn process_cell<'bump>(
        _steps: &Vec<Step<'bump>>,
        pile: &RefCell<Vec<((), ARichFormula<'bump>)>>,
        cells: &Vec<GlobNode<'bump>>,
        input_edges: &mut Vec<Edges<'bump>>,
        edges: &mut Vec<Edges<'bump>>,
    ) {
        for (cell_idx, GlobNode { cell, .. }) in cells.iter().enumerate() {
            for Assignement {
                step,
                args,
                content,
            } in cell.assignements()
            {
                let from = FromNode::CellCall(InnerCellCall {
                    cell_idx,
                    timepoint: StepCall::Step(*step),
                    args: args.clone(),
                });
                let mut pile = pile.borrow_mut();
                pile.clear();
                pile.extend([((), content.shallow_copy())]);

                let iter = FormulaIterator {
                    pile,
                    passed_along: Some(()),
                    flags: IteratorFlags::QUANTIFIER,
                    f: |_, f: ARichFormula<'bump>| match f.as_ref() {
                        RichFormula::Fun(fun, args) => match fun.as_inner() {
                            InnerFunction::TermAlgebra(TermAlgebra::Cell(c)) => {
                                let c = c.memory_cell();
                                let cell = cells.iter().position(|g| g.cell == c).unwrap();
                                let to_node = ToNode::CellCall(InnerCellCall {
                                    cell_idx: cell,
                                    timepoint: StepCall::General(
                                        args.last().unwrap().shallow_copy(),
                                    ),
                                    args: args[..args.len() - 1].iter().cloned().collect(),
                                });
                                (Some(to_node), repeat_n_zip((), [].into()))
                            }
                            InnerFunction::Step(_s) => {
                                let to_node = ToNode::Input(InputCall {
                                    step: StepCall::General(f),
                                });
                                (Some(to_node), repeat_n_zip((), [].into()))
                            }
                            _ => (None, repeat_n_zip((), ArcIntoIter::from(args))),
                        },
                        _ => (None, repeat_n_zip((), [].into())),
                    },
                };

                iter.for_each(|to_node| match &to_node {
                    ToNode::Input(_) => input_edges.push(Edges {
                        from: from.clone(),
                        to: to_node,
                    }),
                    ToNode::CellCall(_) => edges.push(Edges {
                        from: from.clone(),
                        to: to_node,
                    }),
                })
            }
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
}

mod calculate {
    use crate::{
        formula::formula::RichFormula,
        problem::{cell::MemoryCell, step::Step},
    };

    pub struct CellDependancy<'bump> {
        // self_cell: &'pbl MemoryCell,
        pub step_at: Step<'bump>,
        pub self_args: &'bump Vec<RichFormula<'bump>>,
        pub cell: MemoryCell<'bump>,
        pub call_args: &'bump [RichFormula<'bump>],
        pub step_call: &'bump RichFormula<'bump>,
    }

    pub struct InputDependancy<'bump> {
        // self_cell: &'pbl MemoryCell,
        pub step_at: Step<'bump>,
        pub self_args: &'bump [RichFormula<'bump>],
        pub step_call: &'bump RichFormula<'bump>,
    }

    pub enum Dependancy<'bump> {
        Cell(CellDependancy<'bump>),
        Input(InputDependancy<'bump>),
    }
}
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
