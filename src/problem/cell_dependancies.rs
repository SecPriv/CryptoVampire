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

    use super::{empty, from_vec};

    pub struct CellDependancy<'a> {
        // self_cell: &'a MemoryCell,
        pub step_at: &'a Step,
        pub self_args: &'a Vec<RichFormula>,
        pub cell: &'a MemoryCell,
        pub call_args: &'a [RichFormula],
    }

    pub struct InputDependancy<'a> {
        // self_cell: &'a MemoryCell,
        step_at: &'a Step,
        self_args: &'a [RichFormula],
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
                            RichFormula::Fun(fun, _) if fun == input => (
                                Some(Dependancy::Input(InputDependancy {
                                    // self_cell: cell,
                                    step_at: step,
                                    self_args: args,
                                })),
                                empty().into_iter(),
                            ),
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
                                    })),
                                    empty().into_iter(),
                                )
                            }
                            RichFormula::Fun(_, args) => (None, from_vec(args).into_iter()),
                            _ => (None, empty().into_iter()),
                        },
                    )
                },
            )
    }

    fn find_all_dependancies<'a>(pbl: &'a Problem) -> Vec<Dependancy<'a>> {
        pbl.memory_cells
            .values()
            .flat_map(|c| find_dependencies_cell(pbl, c))
            .collect()
    }
}

pub mod graph {

    use itertools::Itertools;

    use crate::{
        formula::{
            formula::RichFormula,
            formula_iterator::{FormulaIterator, IteratorFlags},
        },
        problem::{cell::MemoryCell, problem::Problem, step::Step},
        utils::utils::StackBox,
    };

    use super::{calculate, empty, from_vec};

    struct CellDependancy<'a> {
        // found in which step?
        step_at: Step,
        // with which arguments?
        self_args: &'a Vec<RichFormula>,
        // calling wich other cells? (assuming it is in DependancyGraph.cells)
        cell: usize,
        // with which arguments
        call_args: &'a [RichFormula],
    }
    pub struct DependancyGraph<'a> {
        cells: Vec<&'a MemoryCell>,
        has_input: Vec<bool>,
        dependancies: Vec<Vec<CellDependancy<'a>>>,
        protocol_dependancies: Vec<usize>,
    }

    impl<'a> From<&'a Problem> for DependancyGraph<'a> {
        fn from(pbl: &'a Problem) -> Self {
            let cells = pbl.memory_cells.values().collect_vec();
            let mut has_input = vec![false; cells.len()];
            let dependancies = cells
                .iter()
                .enumerate()
                .map(|(i, cell)| {
                    let mut dep = Vec::new();
                    for d in calculate::find_dependencies_cell(pbl, cell) {
                        match d {
                            calculate::Dependancy::Input(_) => has_input[i] = true,
                            calculate::Dependancy::Cell(calculate::CellDependancy {
                                step_at,
                                self_args,
                                cell,
                                call_args,
                            }) => {
                                let cell = cells.iter().position(|c| c == &cell).unwrap();
                                dep.push(CellDependancy {
                                    step_at: step_at.clone(),
                                    self_args,
                                    cell,
                                    call_args,
                                })
                            }
                        }
                    }
                    dep
                })
                .collect();

            let protocol_dependancies = {
                let pile = pbl
                    .steps
                    .values()
                    .flat_map(|s| [s.message(), s.condition()].into_iter())
                    .collect_vec();

                FormulaIterator::new(
                    StackBox::new(pile),
                    pbl,
                    IteratorFlags::QUANTIFIER,
                    |f, _| match f {
                        RichFormula::Fun(fun, _) if fun.is_cell() => {
                            (Some(fun), empty().into_iter())
                        }
                        RichFormula::Fun(_, args) => (None, from_vec(args).into_iter()),
                        _ => (None, empty().into_iter()),
                    },
                )
            }
            .unique()
            .map(|fun| cells.iter().position(|c| c.name() == fun.name()).unwrap()) // I don't like using names
            .collect();

            DependancyGraph {
                cells,
                has_input,
                dependancies,
                protocol_dependancies,
            }
        }
    }
}
struct PossiblyEmptyIterator<'a, T>(Option<&'a Vec<T>>);
impl<'a, T> PossiblyEmptyIterator<'a, T> {
    fn into_iter(self) -> impl Iterator<Item = &'a T> {
        self.0.into_iter().flat_map(|v| v.iter())
    }
}

fn empty<'a, T>() -> PossiblyEmptyIterator<'a, T> {
    PossiblyEmptyIterator(None)
}

fn from_vec<'a, T>(vec: &'a Vec<T>) -> PossiblyEmptyIterator<'a, T> {
    PossiblyEmptyIterator(Some(vec))
}
