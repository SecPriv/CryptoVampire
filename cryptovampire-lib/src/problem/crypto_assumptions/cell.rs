use std::rc::Rc;

use itertools::{chain, Itertools};

use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula,
        function::builtin::PRED,
        sort::builtins::STEP,
        variable::Variable,
    },
    problem::{cell::Assignement, Problem},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Cell;

impl Cell {
    pub fn generate<'bump>(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        _declarations: &mut Vec<Declaration<'bump>>,
        _env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        let max_var = pbl.protocol().max_var();
        let step_var = Variable {
            id: max_var,
            sort: STEP.as_sort(),
        };
        let max_var = max_var + 1;
        assertions.push(Axiom::Comment("cells".into()));
        assertions.extend(
            pbl.protocol()
                .memory_cells()
                .iter()
                .map(|c| {
                    let vars: Vec<_> = c
                        .args()
                        .iter()
                        .enumerate()
                        .map(|(id, &sort)| Variable {
                            id: id + max_var,
                            sort,
                        })
                        .collect();
                    let _max_var = max_var + vars.len();

                    let nvars: Rc<[_]> = vars.iter().chain([&step_var]).cloned().collect();
                    let cell_call = c.function().f_a(nvars.as_ref());

                    let (positive, negative): (Vec<_>, Vec<_>) = c
                        .assignements()
                        .iter()
                        .map(
                            |Assignement {
                                 step,
                                 args,
                                 content,
                                 fresh_vars,
                             }| {
                                let bvars = step
                                    .free_variables()
                                    .iter()
                                    .chain(fresh_vars.iter())
                                    .cloned()
                                    .collect_vec();
                                let step_call = step.function().f_a(step.free_variables());
                                let ands = formula::ands(
                                    vars.iter()
                                        .zip_eq(args.iter())
                                        .chain([(&step_var, &step_call)])
                                        .map(|(l, r)| formula::meq(l, r)),
                                );

                                (
                                    formula::forall(
                                        bvars.clone(),
                                        ands.shallow_copy() >> formula::meq(&cell_call, content),
                                    ),
                                    formula::forall(bvars, !ands.shallow_copy()),
                                )
                            },
                        )
                        .unzip();
                    // let cell_call = c.function().f_a(nvars.as_slice());
                    let cell_call_prev = c.function().f_a(
                        vars.iter()
                            .cloned()
                            .map_into()
                            .chain([PRED.f_a([step_var])]),
                    );
                    // formula::forall(
                    //     nvars,
                    //     ((!formula::ands(negative))
                    //         >> formula::meq(
                    //             pbl.evaluator.eval(cell_call),
                    //             pbl.evaluator.eval(cell_call_prev),
                    //         ))
                    //         & formula::ands(positive),
                    // )
                    chain!(
                        [formula::forall(
                            nvars.clone().iter().cloned(),
                            (formula::ands(negative))
                                >> formula::meq(
                                    pbl.evaluator().eval(cell_call),
                                    pbl.evaluator().eval(cell_call_prev),
                                )
                        )],
                        positive
                            .into_iter()
                            .map(move |f| formula::forall(nvars.clone().iter().cloned(), f))
                    )
                })
                .flatten()
                .map(Axiom::base),
        );
    }
}
