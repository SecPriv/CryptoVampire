use std::rc::Rc;
use std::sync::Arc;

use bitflags::bitflags;
use derive_builder::Builder;
use itertools::{Itertools, chain};
use log::trace;
use utils::{destvec, implvec};

use crate::formula::formula::{ARichFormula, RichFormula, meq};
use crate::formula::function::InnerFunction;
use crate::formula::function::inner::term_algebra::quantifier::Quantifier;
use crate::formula::function::inner::term_algebra::step_macro::InputOrExec;
use crate::formula::function::inner::term_algebra::{TermAlgebra, step_macro};
use crate::formula::manipulation::{
    FrozenMultipleVarSubst, FrozenSubst, OneVarSubst, Substitution,
};
use crate::formula::utils::Applicable;
use crate::formula::variable::{IntoVariableIter, Variable};
use crate::problem::cell::{Assignement, MemoryCell};
use crate::problem::cell_dependancies::{Ancestors, MacroRef, PreprocessedDependancyGraph};
use crate::problem::step::Step;
bitflags! {
    /// Some flags to control the search.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct UnfoldFlags: u8 {
        /// Look through ta quantifiers
        const UNFOLD_TA_QUANTIFIER = 1 << 0;
        /// Look through inputs
        const UNFOLD_INPUT = 1 << 1;
        /// Look though memory cells
        const UNFOLD_MEMORY_CELLS = 1 << 2;
        /// look though `cond` and `msg`
        const UNFOLD_STEP_MACROS = 1 << 3;
        /// Look through exec
        const UNFOLD_EXEC = 1 << 4;
    }
}
pub const REC_MACRO: UnfoldFlags = UnfoldFlags::UNFOLD_INPUT
    .union(UnfoldFlags::UNFOLD_MEMORY_CELLS)
    .union(UnfoldFlags::UNFOLD_STEP_MACROS);

/// Don't look though anything that looks like a macro
pub const NO_REC_MACRO: UnfoldFlags = UnfoldFlags::all().difference(REC_MACRO);

/// State of the seach
///
/// The struct is design for quick We use a [Rc<[Variable]>] for [UnfoldingState::bound_variables] because we copy the s
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Builder)]
pub struct UnfoldingState<'bump> {
    /// The flag on how deep to look
    #[builder(default)]
    flags: UnfoldFlags,
    /// The variables bound by the search (quantifiers or otherwise)
    #[builder(setter(into), default = "Rc::new([])")]
    bound_variables: Rc<[Variable<'bump>]>, // faster than Vec in our usecase
    /// Some condition to get here
    #[builder(setter(into, strip_option), default)]
    guard: Option<ARichFormula<'bump>>,
}

impl<'bump> Default for UnfoldingState<'bump> {
    fn default() -> Self {
        UnfoldingStateBuilder::default().build().unwrap()
    }
}

impl<'bump> UnfoldingState<'bump> {
    pub fn map_dk<F>(&self, f: F) -> Self
    where
        F: FnOnce(UnfoldFlags) -> UnfoldFlags,
    {
        Self {
            flags: f(self.flags),
            ..self.clone()
        }
    }

    pub fn add_variables(&self, vars: impl IntoIterator<Item = Variable<'bump>>) -> Self {
        let bound_variables: Rc<[_]> = self
            .bound_variables
            .iter()
            .cloned()
            .chain(vars)
            // .unique_by(|v| v.id)
            .collect();
        trace!(
            "adding variables:\n\t[{}] -> [{}]",
            self.bound_variables.iter().join(", "),
            bound_variables.iter().join(", ")
        );
        assert!(bound_variables.iter().all_unique());
        Self {
            bound_variables,
            ..self.clone()
        }
    }

    pub fn bound_variables(&self) -> &[Variable<'bump>] {
        &self.bound_variables
    }

    /// Same as [Self::bound_variables()] but with an owned [Rc]
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

    pub fn deeper_kind(&self) -> UnfoldFlags {
        self.flags
    }
}

/// Container object to ease the use of [Self::unfold].
///
/// Is build through [UnfolderBuilder]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Builder)]
pub struct Unfolder<'bump> {
    #[builder(default)]
    state: UnfoldingState<'bump>,
    #[builder(setter(into))]
    content: ARichFormula<'bump>,
}

impl<'bump> Unfolder<'bump> {
    /// expand a formula once according to the parameters of its [Self::state].
    /// If the formula is a macro like object, then it will expand it (if [Self::state] calls for it), otherwise it does nothing.
    ///
    /// It returns list of new [Unfolder] (possibly empty if nothing needs to be done).
    /// The [Self::state] of thoses [Unfolder] is modified accordingly.
    ///
    ///  - `steps`: a list of steps (where `input` will look)
    ///  - `graph`: the graph of dependancies
    pub fn unfold(
        &self,
        steps: impl IntoIterator<Item = Step<'bump>>,
        graph: &PreprocessedDependancyGraph<'bump>,
    ) -> Vec<Unfolder<'bump>> {
        let deeper_kinds = self.state.deeper_kind();
        match self.content.as_ref() {
            RichFormula::Var(_) => vec![],
            RichFormula::Quantifier(_, arg) => {
                vec![Unfolder {
                    state: self.state.clone(),
                    content: arg.shallow_copy(),
                }]
            }
            RichFormula::Fun(fun, args) => {
                match fun.as_inner() {
					InnerFunction::TermAlgebra(ta) => match ta {
						TermAlgebra::Quantifier(q)
							if deeper_kinds.contains(UnfoldFlags::UNFOLD_TA_QUANTIFIER) =>
						self.unfold_quantifier(q, args),
						TermAlgebra::Cell(c)
							if deeper_kinds.contains(UnfoldFlags::UNFOLD_MEMORY_CELLS) =>
						self.unfold_cell(steps, graph, c.memory_cell(), args),
                        TermAlgebra::Macro(kind) if deeper_kinds.contains(kind.unfold_flag()) => {
                            use step_macro::MacroKind;
                            match kind.into_kind() {
                            MacroKind::Step(kind) => self.unfold_step_macro(args, steps, kind),
                            MacroKind::Rec(kind) => self.unfold_rec_macro(kind, steps, graph, args),
                        } },

						// writting everything down to get notified by the type checker in case of changes
						TermAlgebra::Condition(_)
						| TermAlgebra::Function(_)
						| TermAlgebra::NameCaster(_)
						| TermAlgebra::IfThenElse(_)
						| TermAlgebra::Quantifier(_)
						| TermAlgebra::Cell(_)
                        | TermAlgebra::Macro(_) => vec![],
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
                    InnerFunction::Name(_) | InnerFunction::EvaluatedFun(_) => vec![],
					// InnerFunction::Invalid(_) => iter.collect(), // we continue anyway
				}
            }
        }
    }

    fn unfold_step_macro(
        &self,
        args: &Arc<[ARichFormula<'bump>]>,
        steps: implvec!(Step<'bump>),
        kind: step_macro::MessageOrCondition,
    ) -> Vec<Unfolder<'bump>> {
        destvec!([arg] = args);
        let state_variables = self.state.bound_variables();
        steps
            .into_iter()
            .map(|s| {
                let content = match kind {
                    step_macro::MessageOrCondition::Condition => s.condition_arc(),
                    step_macro::MessageOrCondition::Message => s.message_arc(),
                }
                .shallow_copy();

                let collision_var =
                    make_collision_avoiding_subst(s.free_variables(), state_variables);
                let nvars = s
                    .free_variables()
                    .iter()
                    .map(|v| collision_var.get_var(v))
                    .collect_vec();
                let state = self.state.add_condition(
                    nvars.iter().copied(),
                    meq(arg, s.function().f(nvars.iter().map(ARichFormula::from))),
                );
                Unfolder { state, content }
            })
            .collect_vec()
    }

    fn unfold_cell(
        &self,
        steps: implvec!(Step<'bump>),
        graph: &PreprocessedDependancyGraph<'bump>,
        c: MemoryCell<'bump>,
        args: &[ARichFormula<'bump>],
    ) -> Vec<Unfolder<'bump>> {
        let nstate = self
            .state
            .map_dk(|dk| dk - UnfoldFlags::UNFOLD_MEMORY_CELLS);
        unfold_cell_or_input(steps, graph, MacroRef::Cell(c), &nstate, args).collect()
    }

    fn unfold_rec_macro(
        &self,
        kind: InputOrExec,
        steps: implvec!(Step<'bump>),
        graph: &PreprocessedDependancyGraph<'bump>,
        args: &[ARichFormula<'bump>],
    ) -> Vec<Unfolder<'bump>> {
        let nstate = self.state.map_dk(|dk| dk - kind.unfold_flag());
        unfold_cell_or_input(steps, graph, kind.into_macro_ref(), &nstate, args).collect()
    }

    /// Expand a ta quantifier.
    fn unfold_quantifier(
        &self,
        q: &Quantifier<'bump>,
        args: &Arc<[ARichFormula<'bump>]>,
    ) -> Vec<Unfolder<'bump>> {
        trace!("expanding quantifier:\n\t{q}");
        let substitution = FrozenSubst::new_from(
            q.free_variables.iter().map(|v| v.id).collect_vec(),
            args.iter().cloned().collect_vec(),
        );
        let collistion_avoidance = {
            let to_avoid = chain!(q.free_variables.iter(), self.state.bound_variables())
                .cloned()
                .collect_vec();
            make_collision_avoiding_subst(q.bound_variables.iter(), &to_avoid)
        };
        let new_state = self.state.add_variables(
            q.bound_variables
                .iter()
                .map(|v| collistion_avoidance.get_var(v)),
        );
        let quantifier_iter = q.get_content().into_vec().into_iter().map(|f| Unfolder {
            state: new_state.clone(),
            content: f
                .apply_substitution2(&collistion_avoidance)
                .apply_substitution2(&substitution),
        });
        itertools::chain!(
            // iter,
            quantifier_iter
        )
        .collect()
    }

    pub fn as_tuple(self) -> (ARichFormula<'bump>, UnfoldingState<'bump>) {
        let Unfolder { state, content } = self;
        (content, state)
    }
}

fn unfold_cell_or_input<'b, 'bump>(
    steps: impl IntoIterator<Item = Step<'bump>> + 'b,
    graph: &'b PreprocessedDependancyGraph<'bump>,
    to_expand: MacroRef<'bump>,
    state: &'b UnfoldingState<'bump>,
    args: &'b [ARichFormula<'bump>],
) -> impl Iterator<Item = Unfolder<'bump>> + 'b
where
    'bump: 'b,
{
    let state_variables = state.bound_variables();
    // let max_var = state_variables.iter().map(|v| v.id).max().unwrap_or(0);
    trace!("expand_cell_or_input");
    let Ancestors { input, cells } = graph.ancestors(to_expand).unwrap();
    trace!("-");

    let step_origin = args.last().unwrap();
    let is_input = to_expand.is_input();

    let cells_iter = cells.iter().flat_map(|c| c.assignements().iter()).map(
        move |ma @ Assignement {
                  step,
                  content,
                  fresh_vars,
                  ..
              }| {
            trace!("in assignement\n\t{:}", &ma);
            let vars = step.free_variables();

            let collision_var = make_collision_avoiding_subst(
                chain!(vars.iter(), fresh_vars.iter()),
                state_variables,
            );

            let step_f = step.function().f(vars.iter().map(|v| collision_var.get(v)));

            // let step_origin = step_origin.apply_substitution2(&collision_var);
            // ^^^^^^^^^^^^^^^ this one is unchanged

            let state = state.add_condition(
                itertools::chain!(vars.iter(), fresh_vars.iter()).map(|v| collision_var.get_var(v)),
                if is_input {
                    Step::strict_before(step_f, step_origin.shallow_copy())
                } else {
                    Step::before(step_f, step_origin.shallow_copy())
                },
            );

            Unfolder {
                state,
                content: content.apply_substitution2(&collision_var),
            }
        },
    );
    let input_iter = input
        .then(move || {
            steps.into_iter().flat_map(move |step| {
                trace!("in input");
                let vars = step.free_variables();
                let collision_var = make_collision_avoiding_subst(vars, state_variables);
                let step_f = step.function().f(vars.iter().map(|v| collision_var.get(v)));

                [step.message_arc(), step.condition_arc()]
                    .into_iter()
                    .map(move |content| {
                        let state = state.add_condition(
                            vars.iter().map(|v| collision_var.get_var(v)),
                            Step::strict_before(step_f.shallow_copy(), step_origin.clone()),
                        );

                        Unfolder {
                            state,
                            content: content.apply_substitution2(&collision_var),
                        }
                    })
            })
        })
        .into_iter()
        .flatten();

    itertools::chain!(cells_iter, input_iter)
}

/// create a substitution that remaps `vars` such that it doesn't collide with `base`
fn make_collision_avoiding_subst<'a, 'bump: 'a>(
    vars: implvec!(&'a Variable<'bump>),
    base: &[Variable<'bump>],
) -> FrozenMultipleVarSubst<'bump, Variable<'bump>> {
    let vars = vars.into_iter().cloned().collect_vec();

    let max_var = chain!(base, &vars).map(Variable::id).max().unwrap_or(0) + 1;
    vars.into_iter()
        .filter(|v| base.contains_var(v))
        .map(|v| OneVarSubst {
            id: v.id,
            f: v + max_var,
        })
        .collect()
}

// -----------------------------------------------------------------------------
// ------------------------ conversion implementation --------------------------
// -----------------------------------------------------------------------------

impl Default for UnfoldFlags {
    fn default() -> Self {
        Self::all()
    }
}
