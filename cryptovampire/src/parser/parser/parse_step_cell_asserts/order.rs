use std::sync::Arc;

use crate::parser::{
    ast,
    parser::{
        get_sort,
        parsable_trait::{Parsable, VarProxy},
        Environement,
    },
    E,
};
use cryptovampire_lib::{
    formula::{quantifier::Quantifier, sort::builtins::STEP, variable::Variable},
    problem::protocol::{Ordering, OrderingKind},
};
use utils::implvec;

pub fn parse_orders_with_bvars<'a, 'str, 'bump, B>(
    env: &'a Environement<'bump, 'str>,
    orders: implvec!(&'a ast::Order<'str>),
    bvars: &'a mut Vec<(&'str str, VarProxy<'bump>)>,
) -> Result<B, E>
where
    B: FromIterator<Ordering<'bump>>,
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
) -> Result<Ordering<'bump>, E> {
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
        .zip(0..)
        .map(
            |(
                ast::VariableBinding {
                    variable,
                    type_name,
                    ..
                },
                id,
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

    let t1 = t1.parse(env, bvars, env, Some(STEP.as_sort().into()))?;
    bvars.truncate(variables.len());
    let t2 = t2.parse(env, bvars, env, Some(STEP.as_sort().into()))?;

    let content = match kind {
        ast::OrderOperation::Incompatible => OrderingKind::Exclusive(t1, t2),
        ast::OrderOperation::Lt => OrderingKind::LT(t1, t2),
        ast::OrderOperation::Gt => OrderingKind::LT(t2, t1),
    };

    let quantifier = match quantifier {
        ast::QuantifierKind::Forall => Quantifier::Forall { variables },
        ast::QuantifierKind::Exists => Quantifier::Exists { variables },
    };
    let content = Ordering::new(quantifier, content);
    debug_assert!(content.check().is_ok());

    Ok(content.into())
}
