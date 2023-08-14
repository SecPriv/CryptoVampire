use std::sync::Arc;

use itertools::Itertools;

use crate::container::allocator::ContainerTools;
use crate::container::ScopedContainer;
use crate::formula::function::builtin::INPUT;
use crate::formula::manipulation::OneVarSubst;
use crate::formula::sort::builtins::{CONDITION, MESSAGE};
use crate::formula::variable::Variable;
use crate::implvec;
use crate::parser::parser::{CellCache, FunctionCache};
use crate::parser::{merr, E};
use crate::problem::cell::{Assignement, InnerMemoryCell};
use crate::problem::step::InnerStep;

use super::super::ast;
use super::parsable_trait::Parsable;
use super::state::State;
use super::{Environement, StepCache};

/// parse a step and assign the assignements
///
/// This should be done farily late. Only takes a [StepCache].
///
/// The function returns a [InnerStep] to *maybe* mutlipthread things on day...
fn parse_step<'bump, 'str>(
    env: &Environement<'bump, 'str>,
    step: &StepCache<'str, 'bump>,
    // name: &str,
) -> Result<InnerStep<'bump>, E> {
    let StepCache {
        args,
        args_name,
        ast,
        function,
        step,
    } = step;

    let ast::Step {
        message,
        condition,
        assignements,
        name,
        ..
    } = ast;

    let name = name.name();

    // symbolic
    let state = State::from(env).to_symbolic();
    // the free variables used in the step (i.e., the arguments)
    let free_variables: Arc<[_]> = args
        .iter()
        .enumerate()
        .map(|(id, &sort)| Variable { id, sort })
        .collect();
    // ALL the variables used in the step. We start the free ones
    let mut used_variables: Vec<_> = free_variables.iter().cloned().collect();
    // the variable pile. i.e., free_varible + "in"
    let mut bvars = args_name
        .iter()
        .cloned()
        .zip(free_variables.iter().cloned())
        .chain([(
            "in",
            Variable {
                id: free_variables.len(),
                sort: MESSAGE.clone(),
            },
        )])
        .map(|(name, var)| (name, var.into()))
        .collect_vec();
    // the length of the "static" part of `bvar`, to ease reseting it
    let n = bvars.len();

    // substitution to replace the "in" variable
    let substitution = OneVarSubst {
        id: n - 1,
        f: INPUT.f_a([function.f_a(
            args.iter()
                .enumerate()
                .map(|(id, &sort)| Variable { id, sort }),
        )]),
    };

    //---- parse
    // message
    let message = message.parse(env, &mut bvars, state, Some(MESSAGE.clone().into()))?;
    used_variables.extend(
        // get the variables used
        bvars
            .drain(n..)
            .filter_map(|(_, vp)| vp.try_into_variable()),
    );

    // condition
    let condition = condition.parse(env, &mut bvars, state, Some(CONDITION.clone().into()))?;
    used_variables.extend(
        // get the variables used
        bvars
            .drain(n..)
            .filter_map(|(_, vp)| vp.try_into_variable()),
    );

    // remove the "in"
    let message = message.apply_substitution2(&substitution);
    let condition = condition.apply_substitution2(&substitution);

    //--- Assignemnts
    if let Some(assignements) = assignements {
        for ast::Assignement {
            cell: cell_ast,
            term,
            ..
        } in &assignements.assignements
        {
            // get the cell cache or crash
            let cell_name = cell_ast.name();
            let CellCache {
                args, assignements, ..
            } = env
                .functions
                .get(cell_name)
                .and_then(FunctionCache::as_memory_cell)
                .ok_or(merr(
                    cell_ast.span(),
                    format!("cell {cell_name} doesn't exists"),
                ))?;

            // get the arguments and apply substitution
            let cell_args: Result<Arc<[_]>, _> = cell_ast
                .args()
                .iter()
                .zip(args.iter())
                .map(|(arg, sort)| {
                    // reste `bvars`
                    bvars.truncate(n);
                    arg.parse(env, &mut bvars, state, Some(sort.into()))
                        // remove the "in"
                        .map(|arg| arg.apply_substitution2(&substitution))
                })
                .collect();
            let cell_args = cell_args?;

            // ensure `bvars` is reseted
            bvars.truncate(n);
            let content = term
                .parse(env, &mut bvars, state, Some(MESSAGE.clone().into()))?
                // remove the "in"
                .apply_substitution2(&substitution);

            // add it to the assignements
            assignements.lock().unwrap().push(Assignement {
                step: *step,
                args: cell_args,
                content,
            })
        }
    }

    Ok(InnerStep::new(
        name.to_string(),
        free_variables,
        used_variables.into(),
        condition,
        message,
        *function,
    ))
}

pub fn parse_steps<'a, 'bump, 'str>(
    env: &'a mut Environement<'bump, 'str>, // mut for safety
    steps: implvec!(&'a StepCache<'str, 'bump>),
) -> Result<(), E> {
    steps
        .into_iter()
        .try_for_each(|step_cache @ StepCache { ast, step, .. }| {
            let inner = parse_step(env, step_cache)?;
            let r_err = unsafe {
                <ScopedContainer as ContainerTools<InnerStep<'bump>>>::initialize(step, inner)
            };

            match r_err {
                Err(_) => Err(merr(
                    ast.name.0.span,
                    format!("step {} hash already been defined", ast.name.name()),
                )),
                Ok(()) => Ok(()),
            }
        })
}

pub fn parse_cells<'a, 'str, 'bump>(
    env: &'a mut Environement<'bump, 'str>,
    cells: implvec!(&'a CellCache<'str, 'bump>),
) -> Result<(), E> {
    cells
        .into_iter()
        .try_for_each(|cc @ CellCache { cell, ast, .. }| {
            let inner = parse_cell(env, cc)?;
            let r_err = unsafe {
                <ScopedContainer as ContainerTools<InnerMemoryCell<'bump>>>::initialize(cell, inner)
            };

            match r_err {
                Err(_) => Err(merr(
                    ast.name.span(),
                    format!("step {} hash already been defined", ast.name.name()),
                )),
                Ok(()) => Ok(()),
            }
        })
}

fn parse_cell<'a, 'bump, 'str>(
    _env: &'a mut Environement<'bump, 'str>, // mut for safety
    cell: &CellCache<'str, 'bump>,
) -> Result<InnerMemoryCell<'bump>, E> {
    let CellCache {
        args,
        function,
        assignements,
        ast,
        ..
    } = cell;
    let name = ast.name.name();

    let inner = InnerMemoryCell::new(
        name.to_string(),
        args.iter().cloned().collect(),
        *function,
        assignements.lock().unwrap().iter().cloned().collect(),
    );
    Ok(inner)
}
