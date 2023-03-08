use crate::formula::formula::RichFormula;

use super::{cell::MemoryCell, step::Step};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Dependancy<'a> {
    pub from: CellCall<'a>,
    pub depends_on: OutGoingCall<'a>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DependancyFromStep<'a> {
    pub steps_origin: Vec<Step>,
    pub cell: Option<&'a MemoryCell>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum OutGoingCall<'a> {
    Input(InputCall<'a>),
    Cell(CellCall<'a>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CellCall<'a> {
    pub cell: &'a MemoryCell,
    pub step: StepCall<'a>,
    pub args: &'a [RichFormula],
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InputCall<'a> {
    pub step: StepCall<'a>,
    // pub args: &'a [RichFormula],
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum StepCall<'a> {
    Step(Step),
    General(&'a RichFormula),
}

pub mod graph {

    use itertools::Itertools;

    use crate::{
        formula::{
            formula::RichFormula,
            formula_iterator::{FormulaIterator, IteratorFlags},
        },
        problem::{cell::MemoryCell, problem::Problem, step::Step},
    };

    use super::{
        calculate::{self, find_dependencies_cell, CellDependancy, InputDependancy},
        some_iter, CellCall, Dependancy, DependancyFromStep, InputCall, OutGoingCall, StepCall,
    };
    use anyhow::{Ok, Result};
    use thiserror::Error;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
    pub struct DependancyGraph<'a> {
        cells: Vec<GlobNode<'a>>,
        // calls: Vec<InnerCellCall<'a>>,
        edges: Vec<Edges<'a>>,
        input: InputNode,
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
    struct InputNode {
        pub edges_starts: usize,
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
    struct GlobNode<'a> {
        pub cell: &'a MemoryCell,
        pub edges: Vec<usize>,
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
    struct InnerCellCall<'a> {
        pub cell: usize,
        pub step: StepCall<'a>,
        pub args: &'a [RichFormula],
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
    struct Edges<'a> {
        pub from: FromNode<'a>,
        pub to: ToNode<'a>,
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
    enum FromNode<'a> {
        Input { step: Step },
        CellCall(InnerCellCall<'a>),
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
    enum ToNode<'a> {
        Input(InputCall<'a>),
        CellCall(InnerCellCall<'a>),
    }

    impl<'a> From<&'a Problem> for DependancyGraph<'a> {
        fn from(pbl: &'a Problem) -> Self {
            let mut cells = pbl
                .memory_cells
                .values()
                .map(|cell| GlobNode {
                    cell,
                    edges: vec![],
                })
                .collect_vec();
            cells.sort_unstable_by_key(|g| g.cell);

            let mut edges = cells
                .iter()
                .enumerate()
                .flat_map(|(i, c)| find_dependencies_cell(pbl, &c.cell).map(move |d| (i, d)))
                .map(|(c, d)| match d {
                    calculate::Dependancy::Cell(CellDependancy {
                        step_at,
                        self_args,
                        cell,
                        call_args,
                        step_call,
                    }) => {
                        let df = InnerCellCall {
                            cell: c,
                            step: StepCall::Step(step_at.clone()),
                            args: &self_args[..],
                        };
                        let dt = InnerCellCall {
                            cell: cells.iter().position(|g| cell == g.cell).unwrap(),
                            args: &call_args[..],
                            step: StepCall::General(step_call),
                        };

                        Edges {
                            from: FromNode::CellCall(df),
                            to: ToNode::CellCall(dt),
                        }
                    }
                    calculate::Dependancy::Input(InputDependancy {
                        step_at,
                        self_args,
                        step_call,
                    }) => {
                        let df = InnerCellCall {
                            cell: c,
                            step: StepCall::Step(step_at.clone()),
                            args: &self_args[..],
                        };
                        let dt = InputCall {
                            step: StepCall::General(step_call),
                        };
                        Edges {
                            from: FromNode::CellCall(df),
                            to: ToNode::Input(dt),
                        }
                    }
                })
                .collect_vec();
            for (c, i) in edges.iter().enumerate().filter_map(|(i, e)| match &e.from {
                FromNode::Input { .. } => None,
                FromNode::CellCall(InnerCellCall { cell, .. }) => Some((*cell, i)),
            }) {
                cells[c].edges.push(i)
            }

            let mut pile = Vec::with_capacity(2);
            let start_input = edges.len();
            for s in pbl.steps.values() {
                pile.clear();
                pile.extend([s.message(), s.condition()].into_iter());

                let iter = FormulaIterator::new(
                    &mut pile,
                    pbl,
                    IteratorFlags::QUANTIFIER,
                    |f, _| match f {
                        RichFormula::Fun(fun, args) if fun.is_cell() => {
                            (Some((fun, args)), some_iter(None))
                        }
                        RichFormula::Fun(_, args) => (None, some_iter(Some(args))),
                        _ => (None, some_iter(None)),
                    },
                )
                .unique()
                .map(|(f, args)| {
                    assert!(args.last().is_some());
                    let cell = cells
                        .iter()
                        .position(|c| c.cell.name() == f.name())
                        .unwrap();

                    Edges {
                        from: FromNode::Input { step: s.clone() },
                        to: ToNode::CellCall(InnerCellCall {
                            cell,
                            step: StepCall::General(args.last().unwrap()),
                            args: &args[..(args.len() - 1)],
                        }),
                    }
                });
                edges.extend(iter);
            }

            DependancyGraph {
                cells,
                edges,
                input: InputNode {
                    edges_starts: start_input,
                },
            }
        }
    }

    #[derive(Debug, Error)]
    pub enum DependancyError {
        #[error("Cell not found")]
        MemoryCellNotFound,
    }

    impl<'a> DependancyGraph<'a> {
        /// use None for input
        pub fn find_dependencies(&self, cell: Option<&MemoryCell>) -> Result<Vec<Dependancy<'a>>> {
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

        fn inner_find_dependencies(&self, cell: Option<usize>) -> Vec<Dependancy<'a>> {
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
                        ToNode::CellCall(InnerCellCall { cell, .. }) if not_visited_node[*cell] => {
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
            cell: &MemoryCell,
        ) -> Result<Vec<DependancyFromStep<'a>>> {
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
                                cell: c,
                                step: StepCall::Step(s),
                                ..
                            }),
                        to,
                    } = &self.edges[*i]
                    {
                        assert_eq!(*c, cell);
                        match to {
                            ToNode::Input(_) => (None, self.inner_find_dependencies(None), s),
                            ToNode::CellCall(InnerCellCall { cell, .. }) => {
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
                    (d, s.clone())
                })
                .flat_map(|(d, s)| d.into_iter().map(move |om| (s.clone(), om)));

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
                if !result[dfs].steps_origin.contains(&s) {
                    result[dfs].steps_origin.push(s)
                }
            }

            Ok(result)
        }
    }

    impl<'a> InnerCellCall<'a> {
        fn as_cell_call(&self, graph: &DependancyGraph<'a>) -> CellCall<'a> {
            let InnerCellCall { cell, step, args } = self;
            CellCall {
                cell: graph.cells.get(*cell).unwrap().cell,
                step: step.clone(),
                args,
            }
        }
    }

    impl<'a> Edges<'a> {
        fn as_dependancy(&self, graph: &DependancyGraph<'a>) -> Option<Dependancy<'a>> {
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
    }
}

mod calculate {
    use crate::{
        formula::{
            builtins::functions::INPUT,
            formula::RichFormula,
            formula_iterator::{FormulaIterator, IteratorFlags},
        },
        problem::{
            cell::{Assignement, MemoryCell},
            problem::Problem,
            step::Step,
        },
        utils::utils::StackBox,
    };

    pub struct CellDependancy<'a> {
        // self_cell: &'a MemoryCell,
        pub step_at: &'a Step,
        pub self_args: &'a Vec<RichFormula>,
        pub cell: &'a MemoryCell,
        pub call_args: &'a [RichFormula],
        pub step_call: &'a RichFormula,
    }

    use super::some_iter;

    pub struct InputDependancy<'a> {
        // self_cell: &'a MemoryCell,
        pub step_at: &'a Step,
        pub self_args: &'a [RichFormula],
        pub step_call: &'a RichFormula,
    }

    pub enum Dependancy<'a> {
        Cell(CellDependancy<'a>),
        Input(InputDependancy<'a>),
    }

    pub fn find_dependencies_cell<'a>(
        pbl: &'a Problem,
        cell: &'a MemoryCell,
    ) -> impl Iterator<Item = Dependancy<'a>> {
        let input = INPUT(&pbl.env);
        cell.assignements()
            .iter()
            .zip(std::iter::repeat(input))
            .flat_map(
                move |(
                    Assignement {
                        step,
                        args,
                        content,
                    },
                    input,
                )| {
                    let pile = vec![content];

                    FormulaIterator::new(
                        StackBox::new(pile),
                        pbl,
                        IteratorFlags::QUANTIFIER,
                        move |f, pbl| match f {
                            RichFormula::Fun(fun, iargs) if fun == input => {
                                assert_eq!(iargs.len(), 1);
                                (
                                    Some(Dependancy::Input(InputDependancy {
                                        // self_cell: cell,
                                        step_at: step,
                                        self_args: args,
                                        step_call: iargs.first().unwrap(),
                                    })),
                                    some_iter(None),
                                )
                            }
                            RichFormula::Fun(fun, fargs) if fun.is_cell() => {
                                assert!(fargs.last().is_some());
                                let other_cell = pbl.memory_cells.get(fun.name()).unwrap();
                                let call_args = &fargs[..(fargs.len() - 1)];
                                (
                                    Some(Dependancy::Cell(CellDependancy {
                                        // self_cell: cell,
                                        step_at: step,
                                        self_args: args,
                                        cell: other_cell,
                                        call_args,
                                        step_call: fargs.last().unwrap(),
                                    })),
                                    some_iter(None),
                                )
                            }
                            RichFormula::Fun(_, args) => (None, some_iter(Some(args))),
                            _ => (None, some_iter(None)),
                        },
                    )
                },
            )
    }

    // fn find_all_dependancies<'a>(pbl: &'a Problem) -> Vec<Dependancy<'a>> {
    //     pbl.memory_cells
    //         .values()
    //         .flat_map(|c| find_dependencies_cell(pbl, c))
    //         .collect()
    // }
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
