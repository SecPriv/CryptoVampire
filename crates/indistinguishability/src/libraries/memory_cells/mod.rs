use clap::builder;
use itertools::{Itertools, chain, iproduct, izip};
use quarck::CowArc;
use rustc_hash::FxHashMap;
use utils::econtinue_let;

use crate::libraries::utils::{EggRewriteSink, RefFormulaBuilder, RewriteSink, SyntaxSearcher};
use crate::libraries::{Library, memory_cells};
use crate::protocol::{Assignements, Protocol, SingleAssignement, Step};
use crate::terms::{Formula, FormulaVariableIter, Function, INDEX_EQ, Rewrite, UNFOLD_MEMORY_CELL};
use crate::{Lang, Problem, rexp};

pub struct MemoryCellLib;

impl Library for MemoryCellLib {
    fn add_rewrites(&self, pbl: &mut Problem, sink: &mut impl RewriteSink) {
        add_rewrites(pbl, sink);
    }
}

fn add_rewrites(pbl: &Problem, sink: &mut impl RewriteSink) {
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

pub(crate) fn search_pred_memory_cell<S: SyntaxSearcher + ?Sized>(
    seracher: &S,
    pbl: &Problem,
    builder: &RefFormulaBuilder,
    cell_head: Function,
    cell_args: CowArc<'static, [Formula]>,
    ptcl: &Protocol,
    time: &Formula,
) {
    todo!()
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn search_concrete_memory_cell<S: SyntaxSearcher + ?Sized>(
    seracher: &S,
    pbl: &Problem,
    builder: &RefFormulaBuilder,
    cell_head: Function,
    cell_args: CowArc<'static, [Formula]>,
    ptcl: &Protocol,
    step: &Step,
    step_args: CowArc<'static, [Formula]>,
) {
    let step_id = &step.id;
    let time = rexp!((step_id #(step_args.iter().cloned())*));
    match step.assignements.get(&cell_head) {
        None => search_pred_memory_cell(seracher, pbl, builder, cell_head, cell_args, ptcl, &time),
        Some(
            SingleAssignement {
                assignement_vars,
                parameter_vars,
                value,
            },
        ) => {
            let builder = if builder.is_and() {
                builder.clone()
            } else {
                builder.add_node().and().build()
            };

            let mut subst = FxHashMap::with_capacity_and_hasher(
                assignement_vars.len() + parameter_vars.len(),
                Default::default(),
            );
            let value = value.alpha_rename_if_with(&mut subst, &mut |_| true);

            let vars = chain![assignement_vars.iter(), &step.vars]
                .map(|v| subst.get(v).unwrap_or(v))
                .collect_vec();
            let cond = Formula::and(
                izip!(&vars, chain![cell_args.iter(), step_args.iter()])
                    .map(|(&v, arg)| rexp!((INDEX_EQ #v #arg))),
            );

            {
                let builder = builder
                    .add_node()
                    .condition(!cond.clone())
                    .variables(vars.iter().cloned().cloned())
                    .build();
                search_pred_memory_cell(seracher, pbl, &builder, cell_head, cell_args, ptcl, &time);
            }
            {
                let builder = builder
                    .add_node()
                    .condition(cond)
                    .variables(vars.iter().cloned().cloned())
                    .build();
                seracher.inner_search_formula(pbl, &builder, value);
            }
        }
    }
}
