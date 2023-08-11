use itertools::Itertools;

use crate::formula::function::builtin::INPUT;
use crate::formula::manipulation::{FrozenSubstF, OneVarSubst, OneVarSubstF};
use crate::formula::sort::builtins::{CONDITION, MESSAGE};
use crate::formula::variable::Variable;
use crate::parser::E;
use crate::problem::step::InnerStep;
use crate::utils::utils::AlreadyInitialized;

use super::super::ast;
use super::parsable_trait::Parsable;
use super::state::State;
use super::{Environement, StepCache};

fn parse_step<'bump, 'str>(
    env: &Environement<'bump, 'str>,
    step: &StepCache<'str, 'bump>,
) -> Result<InnerStep<'bump>, E> {
    let StepCache {
        args,
        args_name,
        ast,
        function,
        step,
    } = step;

    let ast::Step {
        span,
        message,
        condition,
        assignements,
        ..
    } = Box::as_ref(ast);

    let state = State::from(env).to_symbolic();
    let mut bvars = args_name
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .chain([("in", MESSAGE.clone())])
        .enumerate()
        .map(|(id, (name, sort))| (name, Variable { id, sort }.into()))
        .collect_vec();
    let n = bvars.len();

    // replace the "in" variable
    let substitution = OneVarSubst {
        id: n - 1,
        f: INPUT.f_a([function.f_a(
            args.iter()
                .enumerate()
                .map(|(id, &sort)| Variable { id, sort }),
        )]),
    };

    // parse
    let message = message.parse(env, &mut bvars, state, Some(MESSAGE.clone().into()))?;
    bvars.truncate(n);
    let condition = condition.parse(env, &mut bvars, state, Some(CONDITION.clone().into()))?;

    let message = message.apply_substitution2(&substitution);
    let condition = condition.apply_substitution2(&substitution);

    todo!()
}
