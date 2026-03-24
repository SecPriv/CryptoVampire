use itertools::{Itertools, chain, iproduct};

use crate::libraries::memory_cells;
use crate::libraries::utils::{EggRewriteSink, RewriteSink};
use crate::protocol::{SingleAssignement, Step};
use crate::terms::{Formula, FormulaVariableIter, Rewrite, UNFOLD_MEMORY_CELL};
use crate::{Lang, Problem, rexp};

pub fn add_rewrites(pbl: &Problem, sink: &mut impl RewriteSink) {
    let memory_cells = pbl.functions().memory_cells().collect_vec();
    let ptcls = pbl.protocols();
    sink.reserve(ptcls.len() * ptcls[0].steps().len() * memory_cells.len());

    for (ptcl, &cell) in iproduct!(ptcls, &memory_cells) {
        let p = ptcl.name().rapp([]);
        for Step {
            id,
            vars: step_vars,
            assignements,
            ..
        } in ptcl.steps()
        {
            let step_varsf = step_vars.into_formula_iter();
            let tau = rexp!((id #step_varsf*));
            let name = format!("unfold cell {cell} step {id}");
            let builder = Rewrite::builder().name(name);
            if let Some(
                a @ SingleAssignement {
                    assignement_vars,
                    parameter_vars,
                    ..
                },
            ) = assignements.get(cell)
            {
                let pvars = parameter_vars.into_formula_iter();
                let formula = a.mk_formula(cell, &tau, &p);
                sink.add_rewrite(
                    pbl,
                    builder
                        .from(rexp!((UNFOLD_MEMORY_CELL (cell #pvars*) #tau #p)))
                        .to(formula)
                        .variables(
                            chain![step_vars, parameter_vars, assignement_vars]
                                .unique()
                                .cloned(),
                        )
                        .build(),
                );
            } else {
                let (mut cvars, formula) = SingleAssignement::mk_default_formula(cell, &tau, &p);
                let fvars = (&cvars).into_formula_iter();
                sink.add_rewrite(
                    pbl,
                    builder
                        .from(rexp!((UNFOLD_MEMORY_CELL (cell #fvars*) #tau #p)))
                        .to(formula)
                        .variables({
                            cvars.extend_from_slice(step_vars);
                            cvars
                        })
                        .build(),
                );
            }
        }
    }
}
