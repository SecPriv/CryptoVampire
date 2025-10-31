use std::rc::Rc;

use itertools::{Itertools, chain};

use crate::environement::environement::Environement;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula;
use crate::formula::function::builtin::PRED;
use crate::formula::sort::builtins::STEP;
use crate::formula::utils::Applicable;
use crate::formula::variable::{Variable, from_usize};
use crate::problem::Problem;
use crate::problem::cell::Assignement;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Cell;

impl Cell {
    #[allow(clippy::ptr_arg)]
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
                .flat_map(|c| {
                    let vars: Vec<_> = c
                        .args()
                        .iter()
                        .zip(0..)
                        .map(|(&sort, id)| Variable {
                            id: id + max_var,
                            sort,
                        })
                        .collect();
                    let _max_var = max_var + from_usize(vars.len());
                    let nvars: Rc<[_]> = vars.iter().chain([&step_var]).cloned().collect();
                    let cell_call = c.function().f(nvars.as_ref());

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
                                let step_call = step.function().f(step.free_variables());
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
                    let cell_call_prev =
                        c.function()
                            .f(vars.iter().cloned().map_into().chain([PRED.f([step_var])]));
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
                .map(Axiom::base),
        );
    }
}
