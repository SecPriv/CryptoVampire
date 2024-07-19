use std::{borrow::Borrow, sync::Arc};

use crate::parser::{
    ast, parser::{
        get_sort,
        parsable_trait::{Parsable, VarProxy},
        Environement,
    }, InputError, MResult, Pstr
};
use cryptovampire_lib::{
    formula::{quantifier::Quantifier, sort::builtins::STEP, variable::Variable},
    problem::protocol::{Ordering, OrderingKind},
};
use utils::{implvec, string_ref::StrRef};

pub fn parse_orders_with_bvars<'a, 'str, 'bump, B, S>(
    env: &'a Environement<'bump, 'str, S>,
    orders: implvec!(&'a ast::Order<'str, S>),
    bvars: &'a mut Vec<(S, VarProxy<'bump>)>,
) -> MResult<B>
where
    B: FromIterator<Ordering<'bump>>,S:Pstr, for <'b> StrRef<'b>:From<&'b S>
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
) -> MResult<Ordering<'bump>> where S:Pstr, for <'b> StrRef<'b>:From<&'b S> {
    let ast::Order {
        quantifier,
        args,
        t1,
        t2,
        kind,
        ..
    } = order;

    let args: Result<Vec<_>, InputError> = args
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
    bvars.extend(args.iter().map(|(name, var)| ((*name).clone(), (*var).into())));
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
