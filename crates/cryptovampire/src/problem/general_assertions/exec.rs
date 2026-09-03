use crate::environement::environement::Environement;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::{ARichFormula, ands, meq};
use crate::formula::function::Function;
use crate::formula::function::builtin::{
    CONDITION_TO_BOOL, HAPPENS_SYMBOLIC, IMPLIES, LESS_THAN_STEP_SYMBOLIC,
};
use crate::formula::sort::builtins::{CONDITION, STEP};
use crate::formula::utils::Applicable;
use crate::formula::variable::{IntoVariableIter, Variable};
use crate::problem::problem::Problem;
use crate::mforall;

/// Emit a named `exec_pred : Step -> Bool` symbol together with its
/// definitional axiom, generalising the hand-written `exec_pred!` / `epred`
/// trick used in the mw / lak-tag add-rewrite models.
///
/// Under `--exec-pred` the symbol is *declared* (seeded into the parse-time
/// namespace by the caller, so models can reference `exec_pred(...)`
/// directly) and here we derive the definition from the protocol's own
/// steps:
///
/// ```text
/// forall (t: Step).
///     evaluate_cond(exec_pred(t)) =
///         evaluate_cond(s_happens(t)) &&
///         and_{S step} (forall (args_S : sorts_S).
///             evaluate_cond(s_lt(S(args_S), t)) => evaluate_cond(cond!(S(args_S))))
/// ```
///
/// i.e. `t` was executed and every step ordered strictly-before `t` (with
/// its guard satisfied, instantiated at the same argument position) was
/// executed too. As a general assertion it is written at the *Bool* level
/// (explicit `evaluate_cond` wrappers), matching how the user-level
/// `epred` definition is normalised by `propagate_evaluate`.
pub fn generate<'bump>(
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    env: &Environement<'bump>,
    pbl: &Problem<'bump>,
) {
    if !env.exec_pred() {
        return;
    }

    // The caller seeds `exec_pred` into the parse-time namespace; reuse that
    // very object so the parsed references and this definition refer to the
    // very same function. The writer already declares every function known to
    // the problem, so no extra declaration is needed here unless the symbol
    // is missing (defensive fallback).
    let found = pbl
        .functions()
        .iter()
        .find(|f| f.name().as_ref() == "exec_pred")
        .copied();
    let exec_pred = match found {
        Some(f) => f,
        None => {
            let f =
                Function::new_user_term_algebra(pbl.container(), "exec_pred", [*STEP], *CONDITION)
                    .main;
            declarations.push(Declaration::FreeFunction(f));
            f
        }
    };

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

    let mut conjuncts: Vec<ARichFormula<'_>> = vec![ecl.f([s_happens.f([t.clone()])])];
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
        let before = ecl.f([s_lt.f([step_term, t.clone().into()])]);
        let after = ecl.f([guard]);
        conjuncts.push(mforall!(vars.into_iter(), { IMPLIES.f([before, after]) }));
    }

    let composite = ands(conjuncts);
    let a = ecl.f([exec_pred.f([t.clone()])]);
    let def = mforall!([t], { meq(a, composite) });

    assertions.push(Axiom::base(def));
}
