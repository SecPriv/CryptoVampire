use std::sync::Arc;

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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum ExpantionStateEnum<'bump> {
    None,
    BoundingVariables(Arc<[Variable<'bump>]>),
    Deeper(InnerExpantionState<'bump>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerExpantionState<'bump> {
    pub bound_variables: Arc<[Variable<'bump>]>,
    pub content: ARichFormula<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ExpantionState<'bump> {
    state: ExpantionStateEnum<'bump>,
    deeper_kind: DeeperKinds,
}

impl<'bump> ExpantionState<'bump> {
    pub fn from_deeper_kind(deeper_kind: DeeperKinds) -> Self {
        Self {
            state: ExpantionStateEnum::None,
            deeper_kind,
        }
    }

    pub fn map_dk<F>(&self, f: F) -> Self
    where
        F: FnOnce(DeeperKinds) -> DeeperKinds,
    {
        Self {
            state: self.state.clone(),
            deeper_kind: f(self.deeper_kind),
        }
    }

    pub fn add_variables(&self, vars: impl IntoIterator<Item = Variable<'bump>>) -> Self {
        Self {
            state: self.state.add_variables(vars),
            deeper_kind: self.deeper_kind,
        }
    }

    pub fn bound_variables(&self) -> Option<&[Variable<'bump>]> {
        self.state.bound_variables()
    }
    pub fn condition(&self) -> Option<&ARichFormula<'bump>> {
        self.state.condition()
    }

    pub fn add_condition(
        &self,
        vars: impl IntoIterator<Item = Variable<'bump>>,
        condition: ARichFormula<'bump>,
    ) -> Self {
        Self {
            state: self.state.add_condition(vars, condition),
            deeper_kind: self.deeper_kind,
        }
    }

    pub fn state(&self) -> &ExpantionStateEnum<'bump> {
        &self.state
    }

    pub fn deeper_kind(&self) -> DeeperKinds {
        self.deeper_kind
    }
}

impl<'bump> ExpantionStateEnum<'bump> {
    pub fn add_variables(&self, vars: impl IntoIterator<Item = Variable<'bump>>) -> Self {
        match self {
            ExpantionStateEnum::None => {
                ExpantionStateEnum::BoundingVariables(vars.into_iter().collect())
            }
            ExpantionStateEnum::BoundingVariables(old_vars) => {
                ExpantionStateEnum::BoundingVariables(
                    vars.into_iter().chain(old_vars.iter().cloned()).collect(),
                )
            }
            ExpantionStateEnum::Deeper(inner) => {
                let InnerExpantionState {
                    bound_variables,
                    content,
                } = inner;
                ExpantionStateEnum::Deeper(InnerExpantionState {
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
            ExpantionStateEnum::None => None,
            ExpantionStateEnum::BoundingVariables(vars) => Some(vars.as_ref()),
            ExpantionStateEnum::Deeper(inner) => Some(inner.bound_variables.as_ref()),
        }
    }

    pub fn condition(&self) -> Option<&ARichFormula<'bump>> {
        match self {
            ExpantionStateEnum::Deeper(inner) => Some(&inner.content),
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

        ExpantionStateEnum::Deeper(InnerExpantionState {
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
    ) -> Vec<ExpantionContent<'bump>> {
        let deeper_kinds = self.state.deeper_kind();
        match self.content.as_ref() {
            RichFormula::Var(_) => vec![],
            RichFormula::Quantifier(_, args) => {
                expand_process_arg(self, Arc::new([args.shallow_copy()])).collect()
            }
            RichFormula::Fun(fun, args) => {
                let iter = (if with_args {
                    Some(expand_process_arg(self, Arc::clone(args)))
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
						TermAlgebra::Input(_) if deeper_kinds.contains(DeeperKinds::INPUT) => {
							let nstate = self.state.map_dk(|dk| {
								dk ^ DeeperKinds::INPUT
							});

							iter
							.chain(expand_process_deeper(steps, graph, None, &nstate, args.as_ref()))
							.collect()},
						TermAlgebra::Cell(c)
							if deeper_kinds.contains(DeeperKinds::MEMORY_CELLS) =>
						{
							let nstate = self.state.map_dk(|dk| {
								dk ^ DeeperKinds::MEMORY_CELLS
							});
							iter.chain(expand_process_deeper(
								steps,
								graph,
								Some(c.memory_cell()),
								&nstate,
								args.as_ref(),
							))
							.collect()
						}

						// writting everything down to get notified by the type checker in case of changes
						TermAlgebra::Condition(_)
						| TermAlgebra::Function(_)
						| TermAlgebra::NameCaster(_)
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
					| InnerFunction::Evaluate(_) |
                    InnerFunction::Name(_) | InnerFunction::EvaluatedFun(_) => iter.collect(),
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

fn expand_process_arg<'a, 'b, 'c, 'bump>(
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
fn expand_process_deeper<'b, 'bump>(
    steps: impl IntoIterator<Item = Step<'bump>> + 'b,
    graph: &DependancyGraph<'bump>,
    deeper: Option<MemoryCell<'bump>>,
    state: &'b ExpantionState<'bump>,
    args: &'b [ARichFormula<'bump>],
) -> impl Iterator<Item = ExpantionContent<'bump>> + 'b
where
    'bump: 'b,
{
    debug_print::debug_println!("process_deeper -> {}:{}:{}", file!(), line!(), column!());
    let Ancestors { input, cells } = graph.ancestors(deeper.clone()).unwrap();
    debug_print::debug_println!("process_deeper -> {}:{}:{}", file!(), line!(), column!());

    let step_origin = args.last().unwrap();
    let is_input = deeper.is_none();

    let cells_iter = cells.into_iter().flat_map(|c| c.assignements().iter()).map(
        move |Assignement { step, content, .. }| {
            let vars = step.free_variables();
            let step_f = step.function().f_a(vars.iter().map(|v| v.into_formula()));

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
        },
    );
    let input_iter = input
        .then(move || {
            steps.into_iter().flat_map(move |step| {
                [step.message_arc(), step.condition_arc()]
                    .into_iter()
                    .map(move |content| {
                        let vars = step.free_variables();
                        let step_f = step.function().f_a(vars.iter().map(|v| v.into_formula()));

                        let state = state.add_condition(
                            vars.iter().cloned(),
                            Step::strict_before(step_origin.clone(), step_f.shallow_copy()),
                        );

                        ExpantionContent {
                            state,
                            content: content.shallow_copy(),
                        }
                    })
            })
        })
        .into_iter()
        .flatten();

    itertools::chain!(cells_iter, input_iter)
}

// -----------------------------------------------------------------------------
// ------------------------ conversion implementation --------------------------
// -----------------------------------------------------------------------------

// impl<'a, 'bump> From<&'a ARichFormula<'bump>> for ExpantionContent<'bump> {
// 	fn from(value: &'a ARichFormula<'bump>) -> Self {
// 		ExpantionContent {
// 			state: ExpantionState::None,
// 			content: value.shallow_copy(),
// 		}
// 	}
// }

// impl<'a, 'bump> From<ARichFormula<'bump>> for ExpantionContent<'bump> {
// 	fn from(value: ARichFormula<'bump>) -> Self {
// 		ExpantionContent {
// 			state: ExpantionState::None,
// 			content: value,
// 		}
// 	}
// }

impl Default for DeeperKinds {
    fn default() -> Self {
        Self::all()
    }
}
