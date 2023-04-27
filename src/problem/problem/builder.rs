use std::{rc::Rc, sync::Arc};

use itertools::Itertools;

use crate::{
    container::Container,
    formula::{
        formula::RichFormula,
        function::{
            builtin::{HAPPENS, LESS_THAN_STEP},
            evaluate::Evaluator,
            term_algebra::name::NameCaster,
            Function,
        },
        sort::{
            builtins::{MESSAGE, NONCE, STEP},
            Sort,
        },
        variable::Variable,
    },
    implvec, mforall,
    problem::{
        cell::{Assignement, MemoryCell},
        crypto_assumptions::CryptoAssumption,
        protocol::Protocol,
        step::Step,
    },
};

use super::Problem;

#[derive(Debug)]
pub struct PblFromParser<'bump> {
    pub llc: LongLivedContent<'bump>,
    pub functions: Vec<Function<'bump>>,
    pub sorts: Vec<Sort<'bump>>,
    pub assertions: Vec<RichFormula<'bump>>,
    pub lemmas: Vec<RichFormula<'bump>>,
    pub order: Vec<TmpOrdering<'bump>>,
    pub query: Box<RichFormula<'bump>>,

    pub steps: Vec<TmpStep<'bump>>,
    pub cells: Vec<TmpCell<'bump>>,
    pub crypto_assertions: Vec<CryptoAssumption<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpStep<'bump> {
    pub name: String,
    pub args: Vec<Variable<'bump>>,
    pub assignements: Vec<TmpAssignements<'bump>>,
    pub message: Box<RichFormula<'bump>>,
    pub condition: Box<RichFormula<'bump>>,
    pub function: Function<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpCell<'bump> {
    pub name: String,
    pub args: Vec<Sort<'bump>>,
    pub function: Function<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpAssignements<'bump> {
    pub cell_idx: usize,
    pub args: Vec<RichFormula<'bump>>,
    pub content: Box<RichFormula<'bump>>,
}

#[derive(Debug)]
pub struct LongLivedContent<'bump> {
    pub container: &'bump Container<'bump>,
    pub evaluator: Arc<Evaluator<'bump>>,
    pub name_caster: Arc<NameCaster<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpOrdering<'bump> {
    pub vars: Vec<Variable<'bump>>,
    pub a: Box<RichFormula<'bump>>,
    pub b: Box<RichFormula<'bump>>,
    pub kind: OrderingKind,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum OrderingKind {
    Lt,
    Diff,
}

impl<'bump> Into<Problem<'bump>> for PblFromParser<'bump> {
    fn into(self) -> Problem<'bump> {
        let PblFromParser {
            llc,
            functions,
            sorts,
            assertions,
            lemmas,
            query,
            steps,
            cells,
            crypto_assertions,
            order,
        } = self;
        let LongLivedContent {
            container,
            evaluator,
            name_caster,
        } = llc;

        let mut assignements = cells.iter().map(|_| vec![]).collect_vec();

        let steps = generate_steps(container, steps, &mut assignements);
        let memory_cells = generate_cells(container, cells, assignements);
        let ordering = generate_order(order);

        let protocol = Protocol {
            graph: todo!(),
            steps,
            memory_cells,
            ordering,
        };

        let functions = functions
            .into_iter()
            .chain(default_functions())
            .unique()
            .collect();
        let sorts = sorts.into_iter().chain(default_sorts()).unique().collect();

        Problem {
            container,
            functions,
            sorts,
            evaluator,
            name_caster,
            protocol,
            crypto_assertions,
            assertions: todo!(),
            query: todo!(),
        }
    }
}

fn generate_order<'bump>(order: implvec!(TmpOrdering<'bump>)) -> Vec<RichFormula<'bump>> {
    order
        .into_iter()
        .map(|TmpOrdering { vars, a, b, kind }| {
            mforall!(vars, {
                match kind {
                    OrderingKind::Lt => LESS_THAN_STEP.f([*a, *b]),
                    OrderingKind::Diff => (!HAPPENS.f([*a])) | (!HAPPENS.f([*b])),
                }
            })
        })
        .collect()
}

fn generate_steps<'bump>(
    container: &'bump Container<'bump>,
    steps: implvec!(TmpStep<'bump>),
    assignements: &mut Vec<Vec<Assignement<'bump>>>,
) -> Vec<Step<'bump>> {
    steps
        .into_iter()
        .map(
            |TmpStep {
                 name,
                 args,
                 assignements: step_assignements,
                 message,
                 condition,
                 function,
             }| {
                let step = unsafe {
                    Step::new_with_function(container, function, name, args, *message, *condition)
                };

                for TmpAssignements {
                    cell_idx,
                    args,
                    content,
                } in step_assignements
                {
                    assignements[cell_idx].push(Assignement {
                        step,
                        args,
                        content: *content,
                    });
                }

                step
            },
        )
        .collect()
}

fn generate_cells<'bump>(
    container: &'bump Container<'bump>,
    cells: implvec!(TmpCell<'bump>),
    assignements: Vec<Vec<Assignement<'bump>>>,
) -> Vec<MemoryCell<'bump>> {
    cells
        .into_iter()
        .zip(assignements.into_iter())
        .map(
            |(
                TmpCell {
                    name,
                    args,
                    function,
                },
                assignements,
            )| {
                unsafe {
                    MemoryCell::new_with_function(container, function, name, args, assignements)
                }
            },
        )
        .collect()
}

macro_rules! default_functions {
    ($($fun:expr),*) => {
        fn default_functions() -> impl Iterator<Item = Function<'static>> {
            [$($fun.clone()),*].into_iter()
        }
    };
}
default_functions!(LESS_THAN_STEP, HAPPENS);

macro_rules! default_sorts {
    ($($fun:expr),*) => {
        fn default_sorts() -> impl Iterator<Item = Sort<'static>> {
            [$($fun.clone()),*].into_iter()
        }
    };
}

default_sorts!(MESSAGE, NONCE, STEP);
