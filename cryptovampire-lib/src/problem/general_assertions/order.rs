use std::env::var;

use itertools::{izip, Itertools};

use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula::{self, ands, forall, meq, ors, RichFormula},
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
        .f_a::<Variable<'bump>>([]);
    let pred = PRED.clone();

    assertions.push(Axiom::comment("ordering"));
    declarations.push(Declaration::Sort(STEP.clone()));

    // general axioms
    assertions.extend(
        // stolen from
        [ // !!!!! leq is *not* reflexive !!!
            mforall!(t1!1:step, t2!2:step;
                {meq(leq.f_a([t1, t2]) & !meq(t1, t2), lt.f_a([t1, t2]))}),
            happens.f_a([init.clone()]), // ax1
            mforall!(t!1:step;
                {happens.f_a([t]) >> leq.f_a([init.shallow_copy(), t.into()])}), // ax2
            mforall!(t!0:step;
                {happens.f_a([t]) >> (meq(t, init) | happens.f_a([pred.f_a([t])]))}), // ax3
            mforall!(t1!1:step, t2!2:step;
                {happens.f_a([t1]) | happens.f_a([t2]) | meq(t1, t2)}), // ax4
            mforall!(t1!1:step, t2!2:step, t3!3:step;
                {(leq.f_a([t1, t2]) & leq.f_a([t2, t3])) >> leq.f_a([t1, t3])}), // ax5
            mforall!(t1!1:step, t2!2:step;
                {(leq.f_a([t1, t2]) & leq.f_a([t2, t1])) >> meq(t1, t2) }), // ax6
            mforall!(t1!1:step, t2!2:step;
                {meq(happens.f_a([t1]) & happens.f_a([t2]), leq.f_a([t1, t2]) | leq.f_a([t2, t1]))}), // ax7
            mforall!(t!0:step;
                {happens.f_a([pred.f_a([t])]) >> leq.f_a([pred.f_a([t]), t.into()])}), // ax8
            mforall!(t!0:step;
                {happens.f_a([t]) >> !meq(pred.f_a([t]), t)}), // ax9
            mforall!(t!0:step;
                {happens.f_a([pred.f_a([t])]) >> happens.f_a([t])}), // ax10
            mforall!(t1!1:step, t2!2:step;
                {(happens.f_a([pred.f_a([t1])]) & happens.f_a([t2])) >>
                    (leq.f_a([t2.into(), pred.f([t1])]) | leq.f_a([t1, t2]))}), // ax11
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
                let t = s.function().f_a(vars);
                let mands = ands(pbl.protocol().steps().iter().map(|s2| {
                    if s == s2 {
                        // A(i) = A(j) => i = j
                        let vars2 = vars.iter().map(|v| (*v) + max_vars).collect_vec();
                        let t2 = s2.function().f_a(&vars2);
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
                        let t2 = s2.function().f_a(&vars2);
                        mforall!(vars2, { !meq(&t, t2) })
                    }
                }));
                mforall!(vars.iter().cloned(), { happens.f_a([t]) >> mands })
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
            let t2 = s.function().f_a(vars);
            mexists!(vars.iter().cloned(), { meq(&t, t2) })
        }));
        mforall!([t], { happens.f_a([t]) >> mors })
    }));

    // user ordering
    assertions.extend(
        pbl.protocol()
            .ordering()
            .iter()
            .map(|o| match o.kind() {
                OrderingKind::LT(a, b) => {
                    RichFormula::Quantifier(o.quantifier().clone(), leq.f_a([a, b]))
                }
                OrderingKind::Exclusive(a, b) => RichFormula::Quantifier(
                    o.quantifier().clone(),
                    !(happens.f_a([a]) & happens.f_a([b])),
                ),
            })
            .map_into()
            .map(Axiom::base),
    );
}
