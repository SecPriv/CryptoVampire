use crate::environement::environement::Environement;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::{ARichFormula, ands, meq};
use crate::formula::function::builtin::{
    CONDITION_TO_BOOL, EXEC_PRED, HAPPENS_SYMBOLIC, IMPLIES, LESS_THAN_STEP_SYMBOLIC,
};
use crate::formula::sort::builtins::STEP;
use crate::formula::utils::Applicable;
use crate::formula::variable::{IntoVariableIter, Variable};
use crate::problem::general_assertions::evaluate::eval_condition;
use crate::problem::problem::Problem;
use crate::mforall;

/// Emit the definitional axiom for the named `exec_pred : Step -> Bool`
/// symbol, generalising the hand-written `pred_exec!` macro / `pred_exec`
/// named-function trick used in the mw / lak-tag add-rewrite models.
///
/// `exec_pred` itself is a builtin ([`crate::formula::function::builtin::EXEC_PRED`],
/// part of `BUILT_IN_FUNCTIONS`), so it is always declared and referencable;
/// under `--exec-pred` we derive its definition from the protocol's own steps:
///
/// ```text
/// forall (t: Step).
///     evaluate_cond(exec_pred(t)) =
///         evaluate_cond(s_happens(t)) &&
///         and_{S step} (forall (args_S : sorts_S).
///             evaluate_cond(s_lt(S(args_S), t)) => <cond!(S(args_S)) pushed down>)
/// ```
///
/// i.e. `t` was executed and every step ordered strictly-before `t` (with its
/// guard satisfied, instantiated at the same argument position) was executed
/// too. The guard is pushed down with `eval_condition` — the *same* procedure
/// the pairwise-fa clauses use — so it renders exactly like the emitted
/// lemmas (`ta$true` → `true`, connectives → Boolean ops, `s_lt`/`s_happens`
/// leaves kept `evaluate_cond`-wrapped), giving the solver the same
/// syntactically-isomorphic shape.
pub fn generate<'bump>(
    assertions: &mut Vec<Axiom<'bump>>,
    _declarations: &mut Vec<Declaration<'bump>>,
    env: &Environement<'bump>,
    pbl: &Problem<'bump>,
) {
    if !env.exec_pred() {
        return;
    }

    // the builtin symbol itself — already known to the parser and the writer
    let exec_pred = *EXEC_PRED;

    let ecl = *CONDITION_TO_BOOL; // evaluate_cond : Condition -> Bool
    let s_lt = *LESS_THAN_STEP_SYMBOLIC; // s_lt : Step, Step -> Condition
    let s_happens = *HAPPENS_SYMBOLIC; // s_happens : Step -> Condition
    let step = *STEP;
    let steps: Vec<_> = pbl
        .protocol()
        .steps()
        .iter()
        .filter(|s| !s.is_init_step())
        .collect();

    // allocate pairwise-distinct variable ids: outer `t`, then one fresh
    // binder per step (mirroring the variable hygiene of the ordering pass)
    let mut next = steps.iter().flat_map(|s| s.free_variables()).max_var();
    let t = Variable::new(next, step);
    next += 1;

    let mut conjuncts: Vec<ARichFormula<'_>> = Vec::with_capacity(steps.len() + 1);
    conjuncts.push(eval_condition(pbl, s_happens.f([t.clone()])));
    for s in steps {
        let n = s.arity();
        let sorts: Vec<_> = s.parameters().cloned().collect();
        let vars: Vec<Variable<'_>> = (0..n)
            .map(|i| Variable::new(next + i, sorts[i as usize]))
            .collect();
        next += n;
        let args: Vec<ARichFormula<'_>> = vars.iter().cloned().map(Into::into).collect();
        let guard = s.apply_condition(&args);
        let step_term = s.function().f(args.clone());
        let before = eval_condition(pbl, s_lt.f([step_term, t.clone().into()]));
        // push `evaluate_cond` down into the step's guard, like the macro did
        let after = eval_condition(pbl, guard);
        conjuncts.push(mforall!(vars.into_iter(), { IMPLIES.f([before, after]) }));
    }

    let composite = ands(conjuncts);
    let a = ecl.f([exec_pred.f([t.clone()])]);
    let def = mforall!([t], { meq(a, composite) });

    assertions.push(Axiom::base(def));
}
