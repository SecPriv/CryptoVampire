use cryptovampire_macros::LocationProvider;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Order<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: L,
    pub quantifier: QuantifierKind,
    pub args: TypedArgument<L, S>,
    pub t1: Term<L, S>,
    pub t2: Term<L, S>,
    pub kind: OrderOperation,
    pub options: Options<L, S>,
    pub guard: Option<Term<L, S>>,
}
boiler_plate!(@ Order, 'a, order ; |p| {
    let span = p.as_span();
    let mut p = p.into_inner();
    let quantifier = p.next().unwrap().try_into()?;
    let args = p.next().unwrap().try_into()?;
    let (guard, nxt) = {
        let n = p.next().unwrap();
        match n.as_rule() {
            Rule::order_guard => {
                let guard = n.into_inner().next()
                                .unwrap().try_into()?;
                (Some(guard), p.next().unwrap())
            }
            _ => (None, n)
        }
    };
    let t1 = nxt.try_into()?;
    let kind = p.next().unwrap().try_into()?;
    let t2 = p.next().unwrap().try_into()?;
    let options = p.next().map(|r| r.try_into().debug_continue())
                    .transpose()?.unwrap_or(Options::empty(span));
    if let Some(_) = p.next() {
        crate::bail_at!(span, "too many arguments")
    }

    Ok(Self {span, quantifier, args, t1, t2, kind, options, guard})
});

impl<'a, L, S: Display> Display for Order<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            quantifier,
            args,
            t1,
            t2,
            kind,
            options,
            ..
        } = self;
        write!(f, "order {quantifier}{args}{{{t1} {kind} {t2}}} {options}")
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum OrderOperation {
    Incompatible,
    Lt,
    Gt,
}
boiler_plate!(OrderOperation, ordering_operation; {
    order_incompatible => Incompatible,
    order_lt => Lt,
    order_gt => Gt
});
impl Display for OrderOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let op = match self {
            OrderOperation::Incompatible => "<>",
            OrderOperation::Lt => "<",
            OrderOperation::Gt => ">",
        };
        write!(f, "{op}")
    }
}
