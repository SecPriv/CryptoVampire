use std::{iter::FusedIterator, sync::Arc, vec::IntoIter};

use itertools::Itertools;

use crate::{
    container::ScopedContainer,
    formula::{
        formula::ARichFormula,
        function::{
            builtin::{HAPPENS, LESS_THAN_STEP, TRUE},
            inner::evaluate::Evaluator,
            inner::term_algebra::name::NameCaster,
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
        cell_dependancies::graph::DependancyGraph,
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
    pub assertions: Vec<ARichFormula<'bump>>,
    pub lemmas: Vec<ARichFormula<'bump>>,
    pub order: Vec<TmpOrdering<'bump>>,
    pub query: ARichFormula<'bump>,

    pub steps: Vec<TmpStep<'bump>>,
    pub cells: Vec<TmpCell<'bump>>,
    pub crypto_assertions: Vec<CryptoAssumption<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpStep<'bump> {
    pub name: String,
    pub args: Vec<Variable<'bump>>,
    pub assignements: Vec<TmpAssignements<'bump>>,
    pub message: ARichFormula<'bump>,
    pub condition: ARichFormula<'bump>,
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
    pub args: Vec<ARichFormula<'bump>>,
    pub content: ARichFormula<'bump>,
}

#[derive(Debug)]
pub struct LongLivedContent<'bump> {
    pub container: &'bump ScopedContainer<'bump>,
    pub evaluator: Arc<Evaluator<'bump>>,
    pub name_caster: Arc<NameCaster<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpOrdering<'bump> {
    pub vars: Vec<Variable<'bump>>,
    pub a: ARichFormula<'bump>,
    pub b: ARichFormula<'bump>,
    pub kind: OrderingKind,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum OrderingKind {
    Lt,
    Diff,
}

#[derive(Debug, Clone)]
/// See `Problem`
struct PrePbl<'bump> {
    container: &'bump ScopedContainer<'bump>,
    functions: Vec<Function<'bump>>,
    sorts: Vec<Sort<'bump>>,
    evaluator: Arc<Evaluator<'bump>>,
    name_caster: Arc<NameCaster<'bump>>,
    protocol: Protocol<'bump>,
    crypto_assertions: Vec<CryptoAssumption<'bump>>,
}

#[derive(Debug)]
pub struct PblIterator<'bump> {
    prepbl: PrePbl<'bump>,

    lemmas: IntoIter<ARichFormula<'bump>>,
    assertions: Vec<ARichFormula<'bump>>,
    query: ARichFormula<'bump>,
}

impl<'bump> PrePbl<'bump> {
    fn to_pbl(
        self,
        assertions: Vec<ARichFormula<'bump>>,
        query: ARichFormula<'bump>,
    ) -> Problem<'bump> {
        let PrePbl {
            container,
            functions,
            sorts,
            evaluator,
            name_caster,
            protocol,
            crypto_assertions,
        } = self;

        Problem {
            container,
            functions,
            sorts,
            evaluator,
            name_caster,
            protocol,
            assertions,
            crypto_assertions,
            query,
        }
    }
}

impl<'bump> Iterator for PblIterator<'bump> {
    type Item = Problem<'bump>;

    fn next(&mut self) -> Option<Self::Item> {
        let nxt = self.lemmas.next()?;
        let old_query = std::mem::replace(&mut self.query, nxt);
        self.assertions.push(old_query);
        Some(
            self.prepbl
                .clone()
                .to_pbl(self.assertions.clone(), self.query.clone()),
        )
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.lemmas.size_hint()
    }
}

impl<'bump> FusedIterator for PblIterator<'bump> {}
impl<'bump> ExactSizeIterator for PblIterator<'bump> {}

impl<'bump> IntoIterator for PblFromParser<'bump> {
    type Item = Problem<'bump>;

    type IntoIter = PblIterator<'bump>;

    fn into_iter(self) -> Self::IntoIter {
        let PblFromParser {
            llc,
            functions,
            sorts,
            assertions,
            mut lemmas,
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
        let graph = DependancyGraph::new(steps.iter().cloned(), memory_cells.iter().cloned());

        let protocol = Protocol {
            graph,
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

        lemmas.push(query);
        let lemmas = lemmas.into_iter();
        PblIterator {
            prepbl: PrePbl {
                container,
                functions,
                sorts,
                evaluator,
                name_caster,
                protocol,
                crypto_assertions,
            },
            lemmas,
            assertions,
            query: TRUE.clone_as_arc(),
        }
    }
}

impl<'bump> Into<Problem<'bump>> for PblFromParser<'bump> {
    fn into(self) -> Problem<'bump> {
        if !self.lemmas.is_empty() {
            eprint!(
                "Using `into` despite having {} lemmas. They will be ignored",
                self.lemmas.len()
            )
        }
        self.into_iter().next().unwrap()
    }
}

// fn compress_quantifier<'bump>(
//     container: &'bump ScopedContainer<'bump>,
//     functions: &mut Vec<Function<'bump>>,
//     f: ARichFormula<'bump>,
// ) -> ARichFormula<'bump> {
//     f.map(&mut |f| match f.as_ref() {
//         RichFormula::Quantifier(q, arg) if q.status().is_condition() => {
//             let fun = Function::new_quantifier_from_quantifier(container, q, arg);
//             let free = match fun.as_inner() {
//                 InnerFunction::TermAlgebra(TermAlgebra::Quantifier(q)) => &q.free_variables,
//                 _ => unreachable!(),
//             };
//             functions.push(fun);
//             fun.f_a(free.iter().map(|v| v.into_formula()).collect())
//         }
//         _ => f,
//     })
// }

fn generate_order<'bump>(order: implvec!(TmpOrdering<'bump>)) -> Vec<ARichFormula<'bump>> {
    order
        .into_iter()
        .map(|TmpOrdering { vars, a, b, kind }| {
            mforall!(vars, {
                match kind {
                    OrderingKind::Lt => LESS_THAN_STEP.f_a([&a, &b]),
                    OrderingKind::Diff => (!HAPPENS.f_a([a])) | (!HAPPENS.f_a([b])),
                }
            })
        })
        .collect()
}

fn generate_steps<'bump>(
    container: &'bump ScopedContainer<'bump>,
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
                    Step::new_with_function(container, function, name, args, message, condition)
                }
                .unwrap();

                for TmpAssignements {
                    cell_idx,
                    args,
                    content,
                } in step_assignements
                {
                    assignements[cell_idx].push(Assignement {
                        step,
                        args: args.into(),
                        content,
                    });
                }

                step
            },
        )
        .collect()
}

fn generate_cells<'bump>(
    container: &'bump ScopedContainer<'bump>,
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
        fn default_functions<'bump>() -> impl Iterator<Item = Function<'bump>> {
            [$(*$fun.shorten_lifetime()),*].into_iter()
        }
    };
}
default_functions!(LESS_THAN_STEP, HAPPENS);

macro_rules! default_sorts {
    ($($fun:expr),*) => {
        fn default_sorts<'bump>() -> impl Iterator<Item = Sort<'bump>> {
            [$(*$fun.shorten_lifetime()),*].into_iter()
        }
    };
}

default_sorts!(MESSAGE, NONCE, STEP);
