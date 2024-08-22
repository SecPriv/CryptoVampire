use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Order<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub quantifier: QuantifierKind,
    pub args: TypedArgument<'a, S>,
    pub t1: Term<'a, S>,
    pub t2: Term<'a, S>,
    pub kind: OrderOperation,
    pub options: Options<'a, S>,
    pub guard: Option<Term<'a, S>>,
}
boiler_plate!(Order<'a>, 'a, order ; |p| {
    let span = p.as_span().into();
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
        bail_at!(&span, "too many arguments")
    }

    Ok(Self {span, quantifier, args, t1, t2, kind, options, guard})
});

impl<'a, S: Display> Display for Order<'a, S> {
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
