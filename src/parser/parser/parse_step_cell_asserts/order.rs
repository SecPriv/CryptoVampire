use std::sync::Arc;

use crate::{
    formula::{
        formula::{ARichFormula, RichFormula},
        function::builtin::{EQUALITY, HAPPENS, LESS_THAN_STEP},
        quantifier::Quantifier,
        sort::builtins::STEP,
        variable::Variable,
    },
    implvec,
    parser::{
        ast,
        parser::{
            get_sort,
            parsable_trait::{Parsable, VarProxy},
            Environement,
        },
        E,
    },
};

pub fn parse_orders_with_bvars<'a, 'str, 'bump, B>(
    env: &'a Environement<'bump, 'str>,
    orders: implvec!(&'a ast::Order<'str>),
    bvars: &'a mut Vec<(&'str str, VarProxy<'bump>)>,
) -> Result<B, E>
where
    B: FromIterator<ARichFormula<'bump>>,
{
    orders
        .into_iter()
        .map(|order| parse_order_with_bvars(env, order, bvars))
        .collect()
}

fn parse_order_with_bvars<'str, 'bump>(
    env: &Environement<'bump, 'str>,
    order: &ast::Order<'str>,
    bvars: &mut Vec<(&'str str, VarProxy<'bump>)>,
) -> Result<ARichFormula<'bump>, E> {
    let ast::Order {
        quantifier,
        args,
        t1,
        t2,
        kind,
        ..
    } = order;

    let args: Result<Vec<_>, _> = args
        .into_iter()
        .enumerate()
        .map(
            |(
                id,
                ast::VariableBinding {
                    variable,
                    type_name,
                    ..
                },
            )| {
                let sort = get_sort(env, type_name.name_span(), type_name.name())?;
                Ok((variable.name(), Variable { id, sort }))
            },
        )
        .collect();
    let args = args?;

    bvars.clear();
    bvars.extend(args.iter().map(|(name, var)| (*name, (*var).into())));
    let variables: Arc<[_]> = args.into_iter().map(|(_, v)| v).collect();

    let t1 = t1.parse(env, bvars, env.into(), Some(STEP.as_sort().into()))?;
    bvars.truncate(variables.len());
    let t2 = t2.parse(env, bvars, env.into(), Some(STEP.as_sort().into()))?;

    let happens = HAPPENS.clone();
    let lt = LESS_THAN_STEP.clone();
    let content = match kind {
        ast::OrderOperation::Incompatible => {
            (happens.f_a([&t1]) & happens.f_a([&t2])) >> EQUALITY.f_a([t1, t2])
        }
        ast::OrderOperation::Lt => lt.f_a([t1, t2]),
        ast::OrderOperation::Gt => lt.f_a([t2, t1]),
    };

    let quantifier = match quantifier {
        ast::QuantifierKind::Forall => Quantifier::Forall { variables },
        ast::QuantifierKind::Exists => Quantifier::Exists { variables },
    };
    let content = RichFormula::Quantifier(quantifier, content);

    Ok(content.into())
}
