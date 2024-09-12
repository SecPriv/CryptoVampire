use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Quantifier<'a, S = &'a str> {
    pub kind: QuantifierKind,
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub vars: TypedArgument<'a, S>,
    pub content: Term<'a, S>,
}
boiler_plate!(Quantifier<'a>, 'a, quantifier; |p| {
  let span = p.as_span().into();
  destruct_rule!(span in [kind, vars, content] = p.into_inner());
  Ok(Self { kind, vars, span, content})
});

impl<'a, S: Display> Display for Quantifier<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            kind,
            vars,
            content,
            ..
        } = self;
        write!(f, "{kind} {vars} {{{content}}}")
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum QuantifierKind {
    Forall,
    Exists,
}
boiler_plate!(QuantifierKind, quantifier_op; {
forall => Forall,
exists => Exists
});

impl Display for QuantifierKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuantifierKind::Forall => write!(f, "∀"),
            QuantifierKind::Exists => write!(f, "∃"),
        }
    }
}
