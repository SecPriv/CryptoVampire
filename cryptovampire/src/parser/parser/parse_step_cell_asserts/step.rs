use std::sync::Arc;

use itertools::Itertools;

use crate::parser::{
    merr,
    parser::{parsable_trait::Parsable, CellCache, FunctionCache},
    E,
};
use cryptovampire_lib::{
    container::{allocator::ContainerTools, ScopedContainer},
    environement::traits::Realm,
    formula::{
        sort::builtins::{CONDITION, MESSAGE},
        variable::{from_usize, uvar, Variable},
    },
    problem::{cell::Assignement, step::InnerStep},
};
use utils::implvec;

use super::super::{super::ast, Environement, StepCache};

/// parse a step and assign the assignements
///
/// This should be done farily late. Only takes a [StepCache].
///
/// The function returns a [InnerStep] to *maybe* mutlipthread things on day...
fn parse_step<'bump, 'str>(
    env: &Environement<'bump, 'str>,
    step_cache: &StepCache<'str, 'bump>,
    // name: &str,
) -> Result<InnerStep<'bump>, E> {
    let StepCache {
        ast,
        function,
        step,
        ..
    } = step_cache;

    let ast::Step {
        message,
        condition,
        assignements,
        name,
        ..
    } = ast;

    let name = name.name();

    // symbolic
    let state = Realm::Symbolic;
    // the free variables used in the step (i.e., the arguments)
    let free_variables: Arc<[_]> = step_cache.args_vars().map(|v| v.variable).collect();

    let mut bvars = step_cache.args_vars_with_input().map_into().collect_vec();
    // the length of the "static" part of `bvar`, to ease reseting it
    let n = bvars.len();

    // substitution to replace the "in" variable
    let substitution = step_cache.substitution_input();

    //---- parse
    // message
    let message = message.parse(env, &mut bvars, &state, Some(MESSAGE.clone().into()))?;
    let msg_used_vars = message.get_used_variables();
    bvars.truncate(n);

    // condition
    let condition = condition.parse(env, &mut bvars, &state, Some(CONDITION.clone().into()))?;
    let cond_used_vars = condition.get_used_variables();
    bvars.truncate(n);

    // remove the "in"
    let message = message.apply_substitution2(&substitution);
    let condition = condition.apply_substitution2(&substitution);

    //--- Assignemnts
    if let Some(assignements) = assignements {
        for ast::Assignement {
            cell: cell_ast,
            term,
            fresh_vars,
            ..
        } in &assignements.assignements
        {
            let fresh_vars = if let Some(vars) = fresh_vars.as_ref() {
                bvars.truncate(n);
                bvars.reserve(vars.bindings.len());
                let vars: Result<Arc<_>, _> = vars
                    .bindings
                    .iter()
                    .zip(0..)
                    .map(
                        |(
                            ast::VariableBinding {
                                type_name,
                                variable,
                                ..
                            },
                            i,
                        )| {
                            let sort = env.find_sort(type_name.name_span(), type_name.name())?;
                            let id = from_usize(n) + i;
                            let var = Variable { id, sort };

                            if env.contains_name_with_var(
                                variable.name(),
                                bvars.iter().map(|(n, _)| *n),
                            ) {
                                Err(merr(
                                    variable.0.span,
                                    format!("name {} is already taken", variable.name()),
                                ))
                            } else {
                                bvars.push((variable.name(), var.into()));
                                Ok(var)
                            }
                        },
                    )
                    .collect();
                vars?
                // env.contains_name_with_var(name, vars)
            } else {
                Arc::new([])
            };

            let n = n + fresh_vars.len();

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
                    arg.parse(env, &mut bvars, &state, Some(sort.into()))
                        // remove the "in"
                        .map(|arg| arg.apply_substitution2(&substitution))
                })
                .collect();
            let cell_args = cell_args?;

            // ensure `bvars` is reseted
            bvars.truncate(n);
            let content = term
                .parse(env, &mut bvars, &state, Some(MESSAGE.clone().into()))?
                // remove the "in"
                .apply_substitution2(&substitution);

            // add it to the assignements
            assignements.lock().unwrap().push(Assignement {
                step: *step,
                args: cell_args,
                content,
                fresh_vars,
            })
        }
    }

    let used_variables = msg_used_vars.into_iter().chain(cond_used_vars).collect();

    Ok(InnerStep::new(
        name.to_string(),
        free_variables,
        used_variables,
        condition,
        message,
        *function,
    ))
}

pub fn parse_steps<'a, 'bump, 'str>(
    env: &'a Environement<'bump, 'str>, // mut for safety
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
                    format!("step {} has already been defined", ast.name.name()),
                )),
                Ok(()) => Ok(()),
            }
        })
}
