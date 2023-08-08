use std::sync::Arc;

use itertools::Itertools;

use crate::{
    formula::{
        formula::{ARichFormula, RichFormula},
        function::{inner::term_algebra::TermAlgebra, InnerFunction},
        variable::Variable,
    },
    problem::{
        cell::{Assignement, MemoryCell},
        cell_dependancies::graph::{Ancestors, DependancyGraph},
        step::Step,
    },
    utils::arc_into_iter::ArcIntoIter,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum ExpantionState<'bump> {
    None,
    BoundingVariables(Arc<[Variable<'bump>]>),
    Deeper(InnerExpantionState<'bump>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerExpantionState<'bump> {
    pub bound_variables: Arc<[Variable<'bump>]>,
    pub content: ARichFormula<'bump>,
}

impl<'bump> ExpantionState<'bump> {
    pub fn add_variables(&self, vars: impl IntoIterator<Item = Variable<'bump>>) -> Self {
        match self {
            ExpantionState::None => ExpantionState::BoundingVariables(vars.into_iter().collect()),
            ExpantionState::BoundingVariables(old_vars) => ExpantionState::BoundingVariables(
                vars.into_iter().chain(old_vars.iter().cloned()).collect(),
            ),
            ExpantionState::Deeper(inner) => {
                let InnerExpantionState {
                    bound_variables,
                    content,
                } = inner;
                ExpantionState::Deeper(InnerExpantionState {
                    bound_variables: bound_variables
                        .iter()
                        .cloned()
                        .chain(vars.into_iter())
                        .collect(),
                    content: content.shallow_copy(),
                })
            }
        }
    }

    pub fn bound_variables(&self) -> Option<&[Variable<'bump>]> {
        match self {
            ExpantionState::None => None,
            ExpantionState::BoundingVariables(vars) => Some(vars.as_ref()),
            ExpantionState::Deeper(inner) => Some(inner.bound_variables.as_ref()),
        }
    }

    pub fn condition(&self) -> Option<&ARichFormula<'bump>> {
        match self {
            ExpantionState::Deeper(inner) => Some(&inner.content),
            _ => None,
        }
    }

    pub fn add_condition(
        &self,
        vars: impl IntoIterator<Item = Variable<'bump>>,
        condition: ARichFormula<'bump>,
    ) -> Self {
        let old_vars = self.bound_variables();
        let old_condition = self.condition();

        let new_vars = match old_vars {
            Some(v) => vars.into_iter().chain(v.iter().cloned()).collect(),
            None => vars.into_iter().collect(),
        };
        let new_condition = match old_condition {
            Some(c) => c.clone() & condition,
            None => condition,
        };

        ExpantionState::Deeper(InnerExpantionState {
            bound_variables: new_vars,
            content: new_condition.shallow_copy(),
        })
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ExpantionContent<'bump> {
    pub state: ExpantionState<'bump>,
    pub content: ARichFormula<'bump>,
}

impl<'bump> ExpantionContent<'bump> {
    /// expand a formula
    ///
    ///  - `steps`: a list of steps (where `input` will look)
    ///  - `graph`: the graph of dependancies
    ///  - `with_args`: when called on `f(*args)` should `args` be returned with the "hidden" terms? (`true` to return `args`, `false` otherwise)
    pub fn expand(
        &self,
        steps: impl IntoIterator<Item = Step<'bump>>,
        graph: &DependancyGraph<'bump>,
        with_args: bool,
        deeper_kinds: DeeperKinds,
    ) -> Vec<ExpantionContent<'bump>> {
        fn process_arg<'a, 'b, 'c, 'bump>(
            expc: &'b ExpantionContent<'bump>,
            args: Arc<[ARichFormula<'bump>]>,
        ) -> impl Iterator<Item = ExpantionContent<'bump>> + 'b
        where
            'bump: 'a,
        {
            ArcIntoIter::from(args)
                .into_iter()
                .map(move |arg| ExpantionContent {
                    state: expc.state.clone(),
                    content: arg.shallow_copy(),
                })
        }

        fn process_deeper<'b, 'bump>(
            steps: impl IntoIterator<Item = Step<'bump>> + 'b,
            graph: &DependancyGraph<'bump>,
            deeper: Option<MemoryCell<'bump>>,
            state: &'b ExpantionState<'bump>,
            args: &'b [ARichFormula<'bump>],
        ) -> impl Iterator<Item = ExpantionContent<'bump>> + 'b
        where
            'bump: 'b,
        {
            let Ancestors { input, cells } = graph.ancestors(deeper.clone()).unwrap();

            let step_origin = args.last().unwrap();
            let is_input = deeper.is_none();
            // let mlt = move |s| {
            //     if is_input {
            //         Step::strict_before(step_origin.clone(), s)
            //     } else {
            //         Step::before(step_origin.clone(), s)
            //     }
            // };

            cells
                .into_iter()
                .flat_map(|c| c.assignements().iter())
                .map(move |Assignement { step, content, .. }| {
                    let vars = step.free_variables();
                    let step_f = step.function().f_a(vars.iter().map(|v| v.into_formula()));
                    // let condition = InnerExpantionState {
                    //     bound_variables: vars.clone(),
                    //     content: if is_input {
                    //         Step::strict_before(step_origin.clone(), step_f)
                    //     } else {
                    //         Step::before(step_origin.clone(), step_f)
                    //     },
                    // };

                    let state = state.add_condition(
                        vars.iter().cloned(),
                        if is_input {
                            Step::strict_before(step_origin.shallow_copy(), step_f)
                        } else {
                            Step::before(step_origin.shallow_copy(), step_f)
                        },
                    );

                    ExpantionContent {
                        state,
                        content: content.shallow_copy(),
                    }
                })
                .chain(
                    if input {
                        None
                    } else {
                        Some(steps.into_iter().flat_map(move |step| {
                            [step.message_arc(), step.condition_arc()].into_iter().map(
                                move |content| {
                                    let vars = step.free_variables();
                                    let step_f =
                                        step.function().f_a(vars.iter().map(|v| v.into_formula()));
                                    // let condition = InnerExpantionState {
                                    //     bound_variables: vars.clone(),
                                    //     content: Step::strict_before(step_origin.clone(), step_f),
                                    // };

                                    let state = state.add_condition(
                                        vars.iter().cloned(),
                                        Step::strict_before(
                                            step_origin.clone(),
                                            step_f.shallow_copy(),
                                        ),
                                    );

                                    ExpantionContent {
                                        state,
                                        content: content.shallow_copy(),
                                    }
                                },
                            )
                        }))
                    }
                    .into_iter()
                    .flatten(),
                )
        }

        match self.content.as_ref() {
            RichFormula::Var(_) => vec![],
            RichFormula::Quantifier(_, args) => {
                process_arg(self, Arc::new([args.shallow_copy()])).collect()
            }
            RichFormula::Fun(fun, args) => {
                let iter = (if with_args {
                    Some(process_arg(self, Arc::clone(args)))
                } else {
                    None
                })
                .into_iter()
                .flatten();

                match fun.as_inner() {
                    InnerFunction::TermAlgebra(ta) => match ta {
                        TermAlgebra::Quantifier(q)
                            if deeper_kinds.contains(DeeperKinds::QUANTIFIER) =>
                        {
                            iter.chain(q.get_content().into_vec().iter().cloned().map(|f| {
                                ExpantionContent {
                                    state: self
                                        .state
                                        .add_variables(q.bound_variables.iter().cloned()),
                                    content: f,
                                }
                            }))
                            .collect()
                        }
                        TermAlgebra::Input(_) if deeper_kinds.contains(DeeperKinds::INPUT) => iter
                            .chain(process_deeper(steps, graph, None, &self.state, args.as_ref()))
                            .collect(),
                        TermAlgebra::Cell(c)
                            if deeper_kinds.contains(DeeperKinds::MEMORY_CELLS) =>
                        {
                            iter.chain(process_deeper(
                                steps,
                                graph,
                                Some(c.memory_cell()),
                                &self.state,
                                args.as_ref(),
                            ))
                            .collect()
                        }

                        // writting everything down to get notified by the type checker in case of changes
                        TermAlgebra::Condition(_)
                        | TermAlgebra::Function(_)
                        | TermAlgebra::Name(_)
                        | TermAlgebra::IfThenElse(_)
                        | TermAlgebra::Quantifier(_)
                        | TermAlgebra::Input(_)
                        | TermAlgebra::Cell(_) => iter.collect(),
                    },
                    InnerFunction::Bool(_)
                    // | Innerfunction::inner::Nonce(_)
                    | InnerFunction::Step(_)
                    | InnerFunction::Subterm(_)
                    | InnerFunction::IfThenElse(_)
                    | InnerFunction::Predicate(_)
                    | InnerFunction::Tmp(_)
                    | InnerFunction::Skolem(_)
                    | InnerFunction::Evaluate(_) => iter.collect(),
                    // InnerFunction::Invalid(_) => iter.collect(), // we continue anyway
                }
            }
        }
    }

    pub fn as_tuple(self) -> (ExpantionState<'bump>, ARichFormula<'bump>) {
        let ExpantionContent { state, content } = self;
        (state, content)
    }
}

impl<'a, 'bump> From<&'a ARichFormula<'bump>> for ExpantionContent<'bump> {
    fn from(value: &'a ARichFormula<'bump>) -> Self {
        ExpantionContent {
            state: ExpantionState::None,
            content: value.shallow_copy(),
        }
    }
}

impl<'a, 'bump> From<ARichFormula<'bump>> for ExpantionContent<'bump> {
    fn from(value: ARichFormula<'bump>) -> Self {
        ExpantionContent {
            state: ExpantionState::None,
            content: value,
        }
    }
}
use bitflags::bitflags;
bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct DeeperKinds: u8 {
        const QUANTIFIER = 1 << 0;
        const INPUT = 1 << 1;
        const MEMORY_CELLS = 1 << 2;
        const NO_MACROS = Self::QUANTIFIER.bits();
    }
}

impl Default for DeeperKinds {
    fn default() -> Self {
        Self::all()
    }
}
