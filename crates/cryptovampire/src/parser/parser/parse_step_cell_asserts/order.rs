use std::sync::Arc;

use crate::parser::{
    ast,
    parser::{
        get_sort,
        parsable_trait::{Parsable, VarProxy},
        Environement,
    },
    Pstr,
};
use crate::{
    formula::{
        quantifier::Quantifier,
        sort::builtins::{BOOL, STEP},
        variable::Variable,
    },
    problem::protocol::{Ordering, OrderingKind},
};
use utils::{implvec, string_ref::StrRef};

pub fn parse_orders_with_bvars<'a, 'str, 'bump, B, S>(
    env: &'a Environement<'bump, 'str, S>,
    orders: implvec!(&'a ast::Order<'str, S>),
    bvars: &'a mut Vec<(S, VarProxy<'bump>)>,
) -> crate::Result<B>
where
    B: FromIterator<Ordering<'bump>>,
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    orders
        .into_iter()
        .map(|order| parse_order_with_bvars(env, order, bvars))
        .collect()
}

fn parse_order_with_bvars<'str, 'bump, S>(
    env: &Environement<'bump, 'str, S>,
    order: &ast::Order<'str, S>,
    bvars: &mut Vec<(S, VarProxy<'bump>)>,
) -> crate::Result<Ordering<'bump>>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    let ast::Order {
        quantifier,
        args,
        t1,
        t2,
        kind,
        guard,
        ..
    } = order;

    let args: crate::Result<Vec<_>> = args
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
                let sort = get_sort(env, type_name.name_span(), type_name.name().borrow())?;
                Ok((variable.name(), Variable { id, sort }))
            },
        )
        .collect();
    let args = args?;

    bvars.clear();
    bvars.extend(
        args.iter()
            .map(|(name, var)| ((*name).clone(), (*var).into())),
    );
    let variables: Arc<[_]> = args.into_iter().map(|(_, v)| v).collect();

    let guard = guard
        .as_ref()
        .map(|guard| guard.parse(env, bvars, env, Some(BOOL.as_sort().into())))
        .transpose()?
        .unwrap_or_default();
    bvars.truncate(variables.len());

    let t1 = t1.parse(env, bvars, env, Some(STEP.as_sort().into()))?;
    bvars.truncate(variables.len());
    let t2 = t2.parse(env, bvars, env, Some(STEP.as_sort().into()))?;
    bvars.truncate(variables.len());

    let content = match kind {
        ast::OrderOperation::Incompatible => OrderingKind::Exclusive(t1, t2),
        ast::OrderOperation::Lt => OrderingKind::LT(t1, t2),
        ast::OrderOperation::Gt => OrderingKind::LT(t2, t1),
    };

    let quantifier = match quantifier {
        ast::QuantifierKind::Forall => Quantifier::Forall { variables },
        ast::QuantifierKind::Exists => Quantifier::Exists { variables },
    };

    let content = Ordering::new_guarded(quantifier, content, guard);
    debug_assert!(content.check().is_ok());
    Ok(content)
}
