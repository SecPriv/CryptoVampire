use itertools::{izip, Itertools};

use crate::formula::utils::Applicable;
use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula::{ands, meq, ors, RichFormula},
        function::builtin::{HAPPENS, LESS_THAN_EQ_STEP, LESS_THAN_STEP, PRED},
        sort::builtins::STEP,
        variable::{IntoVariableIter, Variable},
    },
    mexists, mforall,
    problem::{problem::Problem, protocol::OrderingKind},
};

pub fn generate<'bump>(
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    _: &Environement<'bump>,
    pbl: &Problem<'bump>,
) {
    let lt = LESS_THAN_STEP.clone();
    let leq = LESS_THAN_EQ_STEP.clone();
    let happens = HAPPENS.clone();
    let step = STEP.clone();
    let init = &pbl
        .protocol()
        .init_step()
        .function()
        .f::<Variable<'bump>, _>([]);
    let pred = PRED.clone();

    assertions.push(Axiom::comment("ordering"));
    declarations.push(Declaration::Sort(STEP.clone()));

    // general axioms
    assertions.extend(
        // stolen from
        [
            // !!!!! leq is *not* reflexive !!!
            mforall!(t1!1:step, t2!2:step;
                {meq(leq.f([t1, t2]) & !meq(t1, t2), lt.f([t1, t2]))}),
            happens.f([init.clone()]), // ax1
            mforall!(t!1:step;
                {happens.f([t]) >> leq.f([init.shallow_copy(), t.into()])}), // ax2
            mforall!(t!0:step;
                {happens.f([t]) >> (meq(t, init) | happens.f([pred.f([t])]))}), // ax3
            mforall!(t1!1:step, t2!2:step;
                {happens.f([t1]) | happens.f([t2]) | meq(t1, t2)}), // ax4
            mforall!(t1!1:step, t2!2:step, t3!3:step;
                {(leq.f([t1, t2]) & leq.f([t2, t3])) >> leq.f([t1, t3])}), // ax5
            mforall!(t1!1:step, t2!2:step;
                {(leq.f([t1, t2]) & leq.f([t2, t1])) >> meq(t1, t2) }), // ax6
            mforall!(t1!1:step, t2!2:step;
                {meq(happens.f([t1]) & happens.f([t2]), leq.f([t1, t2]) | leq.f([t2, t1]))}), // ax7
            mforall!(t!0:step;
                {happens.f([pred.f([t])]) >> leq.f([pred.f([t]), t.into()])}), // ax8
            mforall!(t!0:step;
                {happens.f([t]) >> !meq(pred.f([t]), t)}), // ax9
            mforall!(t!0:step;
                {happens.f([pred.f([t])]) >> happens.f([t])}), // ax10
            mforall!(t1!1:step, t2!2:step;
                {(happens.f([pred.f([t1])]) & happens.f([t2])) >>
                    (leq.f([t2.into(), pred.apply([t1])]) | leq.f([t1, t2]))}), // ax11
        ]
        .into_iter()
        .map(Axiom::theory), // .chain(pbl.protocol().ordering().iter().cloned().map(Axiom::base)),
    );

    // specific to the protocol
    assertions.extend(
        // algebra distinctiveness #1
        pbl.protocol()
            .steps()
            .iter()
            .map(|s| {
                let vars = s.free_variables();
                let max_vars = vars.max_var();
                let t = s.function().f(vars);
                let mands = ands(pbl.protocol().steps().iter().map(|s2| {
                    if s == s2 {
                        // A(i) = A(j) => i = j
                        let vars2 = vars.iter().map(|v| (*v) + max_vars).collect_vec();
                        let t2 = s2.function().f(&vars2);
                        mforall!(vars2.iter().cloned(), {
                            meq(&t, t2) >> ands(izip!(vars, &vars2).map(|(v1, v2)| meq(v1, v2)))
                        })
                    } else {
                        // A(i) != B(j)
                        let vars2 = s2
                            .free_variables()
                            .iter()
                            .map(|v| (*v) + max_vars)
                            .collect_vec();
                        let t2 = s2.function().f(&vars2);
                        mforall!(vars2, { !meq(&t, t2) })
                    }
                }));
                mforall!(vars.iter().cloned(), { happens.f([t]) >> mands })
            })
            .map(Axiom::base),
    );

    assertions.push(Axiom::base({
        // algebra exhaustiveness
        let steps = pbl.protocol().steps();
        let max_var = steps.iter().flat_map(|s| s.free_variables()).max_var();
        let t = Variable::new(max_var, step);
        let mors = ors(steps.iter().map(|s| {
            let vars = s.free_variables();
            let t2 = s.function().f(vars);
            mexists!(vars.iter().cloned(), { meq(&t, t2) })
        }));
        mforall!([t], { happens.f([t]) >> mors })
    }));

    // user ordering
    assertions.extend(
        pbl.protocol()
            .ordering()
            .iter()
            .map(|o| {
                let inner = match o.kind() {
                    OrderingKind::LT(a, b) => leq.f([a, b]),
                    OrderingKind::Exclusive(a, b) => !(happens.f([a]) & happens.f([b])),
                };
                RichFormula::Quantifier(o.quantifier().clone(), o.guard().clone() >> inner)
            })
            .map_into()
            .map(Axiom::base),
    );
}
