use std::{rc::Rc, sync::Arc};

use crate::{
    formula::{
        formula::{ARichFormula, RichFormula},
        function::{inner::term_algebra::TermAlgebra, InnerFunction},
        manipulation::FrozenSubst,
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
use itertools::Itertools;
use log::trace;
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
pub struct ExpantionState<'bump> {
    deeper_kind: DeeperKinds,
    bound_variables: Rc<[Variable<'bump>]>, // faster that Vec in our usecase
    // substitution: Rc<Option<FrozenSubstF<'bump, 'bump>>>,
    guard: Option<ARichFormula<'bump>>,
}

impl<'bump> Default for ExpantionState<'bump> {
    fn default() -> Self {
        Self {
            deeper_kind: Default::default(),
            bound_variables: Rc::new([]),
            guard: Default::default(),
            // substitution: Default::default(),
        }
    }
}

impl<'bump> ExpantionState<'bump> {
    pub fn from_deeper_kind(deeper_kind: DeeperKinds) -> Self {
        Self {
            deeper_kind,
            ..Default::default()
        }
    }

    pub fn from_deeped_kind_and_vars(
        deeper_kind: DeeperKinds,
        vars: Rc<[Variable<'bump>]>,
    ) -> Self {
        Self {
            deeper_kind,
            bound_variables: vars,
            ..Default::default()
        }
    }

    pub fn map_dk<F>(&self, f: F) -> Self
    where
        F: FnOnce(DeeperKinds) -> DeeperKinds,
    {
        Self {
            deeper_kind: f(self.deeper_kind),
            ..self.clone()
        }
    }

    pub fn add_variables(&self, vars: impl IntoIterator<Item = Variable<'bump>>) -> Self {
        let bound_variables: Rc<[_]> = self
            .bound_variables
            .iter()
            .cloned()
            .chain(vars)
            .unique_by(|v| v.id)
            .collect();
        trace!(
            "adding variables:\n\t[{}] -> [{}]",
            self.bound_variables.iter().join(", "),
            bound_variables.iter().join(", ")
        );
        Self {
            bound_variables,
            ..self.clone()
        }
    }

    pub fn bound_variables(&self) -> &[Variable<'bump>] {
        &self.bound_variables
    }

    pub fn owned_bound_variable(&self) -> Rc<[Variable<'bump>]> {
        self.bound_variables.clone()
    }

    pub fn condition(&self) -> Option<&ARichFormula<'bump>> {
        self.guard.as_ref()
    }

    pub fn add_condition(
        &self,
        vars: impl IntoIterator<Item = Variable<'bump>>,
        condition: ARichFormula<'bump>,
    ) -> Self {
        let new = self.add_variables(vars);
        let guard = Some(
            new.guard
                .map(|f| f & condition.shallow_copy())
                .unwrap_or(condition),
        );
        Self { guard, ..new }
    }

    // pub fn state(&self) -> &ExpantionStateEnum<'bump> {
    //     &self.state
    // }

    pub fn deeper_kind(&self) -> DeeperKinds {
        self.deeper_kind
    }

    // pub fn add_substitution(
    //     &self,
    //     vars_idx: implvec!(usize),
    //     formulas: implvec!(ARichFormula<'bump>),
    // ) -> Self {
    //     let new = self.clone();
    //     let substitution = Rc::new(Some(if let Some(subst) = new.substitution.as_ref() {
    //         subst.extend_clone(vars_idx, formulas)
    //     } else {
    //         let mut vars_idx = vars_idx.into_iter().peekable();
    //         if let Some(_) = vars_idx.peek() {
    //             FrozenSubstF::new(vars_idx.collect(), formulas.into_iter().collect())
    //         } else {
    //             return new;
    //         }
    //     }));
    //     Self {
    //         substitution,
    //         ..new
    //     }
    // }

    // pub fn substitution(&self) -> &Option<FrozenSubst<'_, ARichFormula<'_>>> {
    //     self.substitution.as_ref()
    // }
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
            RichFormula::Quantifier(_, arg) => {
                expand_process_arg(self, Arc::new([arg.shallow_copy()])).collect()
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
                            trace!("expanding quantifier:\n\t{q}");
                            let substitution = FrozenSubst::new_from(
                                q.free_variables.iter().map(|v| v.id).collect_vec(), args.iter().cloned().collect_vec());
                            let new_state = self
										.state
										.add_variables(q.bound_variables.iter().cloned())
                                        // .add_substitution(q.free_variables.iter().map(|v| v.id), args.iter().cloned())
                                        ;
                            let quantifier_iter = q.get_content().into_vec().into_iter().map(|f| {
								ExpantionContent {
									state: new_state.clone(),
									content: f.apply_substitution2(&substitution),
								}
							});

                            itertools::chain!(
                                // iter,
                                quantifier_iter)
							.collect()
						}
						TermAlgebra::Input(_) if deeper_kinds.contains(DeeperKinds::INPUT) => {
							let nstate = self.state.map_dk(|dk| {
								dk - DeeperKinds::INPUT
							});

							iter
							.chain(expand_process_deeper(steps, graph, None, &nstate, args.as_ref()))
							.collect()},
						TermAlgebra::Cell(c)
							if deeper_kinds.contains(DeeperKinds::MEMORY_CELLS) =>
						{
							let nstate = self.state.map_dk(|dk| {
								dk - DeeperKinds::MEMORY_CELLS
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
/// `deeper` is [None] if comming from an input
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
    trace!("process_deeper -> {}:{}:{}", file!(), line!(), column!());
    let Ancestors { input, cells } = graph.ancestors(deeper.clone()).unwrap();
    trace!("process_deeper -> {}:{}:{}", file!(), line!(), column!());

    let step_origin = args.last().unwrap();
    let is_input = deeper.is_none();

    let cells_iter = cells.into_iter().flat_map(|c| c.assignements().iter()).map(
        move |Assignement {
                  step,
                  content,
                  fresh_vars,
                  ..
              }| {
            let vars = step.free_variables();
            let step_f = step.function().f_a(vars.iter().map(|v| v.into_formula()));

            let state = state.add_condition(
                itertools::chain!(vars.iter(), fresh_vars.iter()).cloned(),
                if is_input {
                    Step::strict_before(step_f, step_origin.shallow_copy())
                } else {
                    Step::before(step_f, step_origin.shallow_copy())
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
                            Step::strict_before(step_f.shallow_copy(), step_origin.clone()),
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

impl Default for DeeperKinds {
    fn default() -> Self {
        Self::all()
    }
}
