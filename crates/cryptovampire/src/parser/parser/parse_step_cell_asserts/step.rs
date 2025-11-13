use std::sync::Arc;

use itertools::Itertools;
use log::trace;
use logic_formula::AsFormula;
use utils::implvec;
use utils::string_ref::StrRef;
use utils::traits::NicerError;

use super::super::super::ast;
use super::super::{Environement, StepCache};
use crate::container::ScopedContainer;
use crate::container::allocator::ContainerTools;
use crate::environement::traits::Realm;
use crate::error::{BaseContext, BaseError, CVContext, ExtraOption};
use crate::formula::sort::builtins::{CONDITION, MESSAGE};
use crate::formula::variable::{Variable, from_usize};
use crate::parser::Pstr;
use crate::parser::parser::parsable_trait::Parsable;
use crate::parser::parser::{CellCache, FunctionCache};
use crate::problem::cell::Assignement;
use crate::problem::step::InnerStep;

/// parse a step and assign the assignements
///
/// This should be done farily late. Only takes a [StepCache].
///
/// The function returns a [InnerStep] to *maybe* mutlipthread things on day...
fn parse_step<'bump, 'str, S>(
    env: &Environement<'bump, 'str, S>,
    step_cache: &StepCache<'str, 'bump, S>,
    // name: &str,
) -> crate::Result<InnerStep<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
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
    let message = message
        .parse(env, &mut bvars, &state, Some((*MESSAGE).into()))
        .debug_continue()?;
    let msg_used_vars = (&message).used_vars_iter();
    bvars.truncate(n);

    // condition
    let condition = condition
        .parse(env, &mut bvars, &state, Some((*CONDITION).into()))
        .debug_continue()?;
    let cond_used_vars = (&condition).used_vars_iter();
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
                let vars: crate::Result<Arc<_>> = vars
                    .bindings
                    .iter()
                    .zip(0..)
                    .map(
                        |(
                            ast::VariableBinding::<_> {
                                type_name,
                                variable,
                                ..
                            },
                            i,
                        )| {
                            let sort =
                                env.find_sort(type_name.name_span(), type_name.name().borrow())?;
                            let id = from_usize(n) + i;
                            let var = Variable { id, sort };

                            if env.contains_name_with_var(
                                variable.name().borrow(),
                                bvars.iter().map(|(n, _)| n.borrow()),
                            ) {
                                BaseError::duplicate_symbol(&"name", variable)
                                    .with_location(variable)
                            } else {
                                bvars.push((variable.name().clone(), var.into()));
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
                .get(cell_name.borrow())
                .and_then(FunctionCache::as_memory_cell)
                .unknown_symbol(cell_ast, &"cell", cell_name)?;

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
                .parse(env, &mut bvars, &state, Some((*MESSAGE).into()))?
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

pub fn parse_steps<'a, 'bump, 'str, S>(
    env: &'a Environement<'bump, 'str, S>, // mut for safety
    steps: implvec!(&'a StepCache<'str, 'bump, S>),
) -> crate::Result<()>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    steps
        .into_iter()
        .try_for_each(|step_cache @ StepCache { ast, step, .. }| {
            trace!("parsing step {}", ast.name);
            let inner = parse_step(env, step_cache).debug_continue()?;
            let r_err = unsafe {
                <ScopedContainer<'bump> as ContainerTools<InnerStep<'bump>>>::initialize(
                    step, inner,
                )
            };

            r_err.with_context(&ast.name, || "step already defined")
        })
}
