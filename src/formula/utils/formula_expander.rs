use std::{iter::repeat, path::Iter, rc::Rc};

use itertools::Itertools;

use crate::{
    formula::{
        formula::{exists, RichFormula},
        function::{term_algebra::TermAlgebra, InnerFunction},
    },
    problem::{
        cell::{Assignement, MemoryCell},
        cell_dependancies::{
            graph::{Ancestors, DependancyGraph},
            Dependancy,
        },
        step::Step,
    },
    utils::vecref::VecRef,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum ExpantionState<'bump> {
    None,
    Deeper(Rc<RichFormula<'bump>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ExpantionContent<'a, 'bump> {
    pub state: ExpantionState<'bump>,
    pub content: &'a RichFormula<'bump>,
}

impl<'a, 'bump> ExpantionContent<'a, 'bump>
where
    'bump: 'a,
{
    pub fn expand(
        &self,
        steps: impl IntoIterator<Item = Step<'bump>>,
        graph: &DependancyGraph<'bump>,
    ) -> Vec<ExpantionContent<'a, 'bump>> {
        fn process_arg<'a, 'b, 'bump>(
            expc: &'b ExpantionContent<'a, 'bump>,
            args: &'a Vec<RichFormula<'bump>>,
        ) -> impl Iterator<Item = ExpantionContent<'a, 'bump>> + 'b
        where
            'bump: 'a,
        {
            args.iter().map(move |arg| ExpantionContent {
                state: expc.state.clone(),
                content: arg,
            })
        }

        fn process_deeper<'a, 'bump>(
            steps: impl IntoIterator<Item = Step<'bump>>,
            graph: &DependancyGraph<'bump>,
            deeper: Option<&MemoryCell<'bump>>,
            args: &'a Vec<RichFormula<'bump>>,
        ) -> impl Iterator<Item = ExpantionContent<'a, 'bump>>
        where
            'bump: 'a,
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
                .map(
                    move |Assignement {
                              step,
                              args,
                              content,
                          }| {
                        let vars = step.free_variables();
                        let step_f = step.function().f(vars.iter().map(|v| v.into_formula()));
                        let condition = exists(
                            vars.clone(),
                            if is_input {
                                Step::strict_before(step_origin.clone(), step_f)
                            } else {
                                Step::before(step_origin.clone(), step_f)
                            },
                        );

                        ExpantionContent {
                            state: ExpantionState::Deeper(Rc::new(condition)),
                            content,
                        }
                    },
                )
                .chain(
                    if input {
                        None
                    } else {
                        Some(steps.into_iter().flat_map(move |step| {
                            [step.message(), step.condition()]
                                .into_iter()
                                .map(move |content| {
                                    let vars = step.free_variables();
                                    let step_f =
                                        step.function().f(vars.iter().map(|v| v.into_formula()));
                                    let condition = exists(
                                        vars.clone(),
                                        Step::strict_before(step_origin.clone(), step_f),
                                    );

                                    ExpantionContent {
                                        state: ExpantionState::Deeper(Rc::new(condition)),
                                        content,
                                    }
                                })
                        }))
                    }
                    .into_iter()
                    .flatten(),
                )
        }

        match self.content {
            RichFormula::Var(_) => vec![],
            RichFormula::Quantifier(_, args) => process_arg(self, args).collect(),
            RichFormula::Fun(fun, args) => {
                let iter = process_arg(self, args);
                match fun.as_ref() {
                    InnerFunction::TermAlgebra(ta) => match ta {
                        TermAlgebra::Condition(_)
                        | TermAlgebra::Function(_)
                        | TermAlgebra::IfThenElse => iter.collect(),
                        TermAlgebra::Quantifier(q) => iter
                            .chain(q.get_content().into_vec().iter().map(|f| ExpantionContent {
                                state: self.state.clone(),
                                content: *f,
                            }))
                            .collect(),
                        TermAlgebra::Input => iter
                            .chain(process_deeper(steps, graph, None, args))
                            .collect(),
                        TermAlgebra::Cell(c) => iter
                            .chain(process_deeper(steps, graph, Some(c.memory_cell()), args))
                            .collect(),
                    },
                    InnerFunction::Bool(_)
                    | InnerFunction::Nonce(_)
                    | InnerFunction::Step(_)
                    | InnerFunction::Subterm(_)
                    | InnerFunction::IfThenElse(_)
                    | InnerFunction::Predicate(_)
                    | InnerFunction::Evaluate(_) => iter.collect(),
                }
            }
        }
    }
}

impl<'a, 'bump> From<&'a RichFormula<'bump>> for ExpantionContent<'a, 'bump> {
    fn from(value: &'a RichFormula<'bump>) -> Self {
        ExpantionContent {
            state: ExpantionState::None,
            content: value,
        }
    }
}
