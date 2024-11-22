use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Quantifier<'str, S> {
    pub kind: QuantifierKind,
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: ASTLocation<'str>,
    pub vars: TypedArgument<'str, S>,
    pub content: Term<'str, S>,
}
boiler_plate!(@ Quantifier, 'a, quantifier; |p| {
  let span = p.as_span();
  destruct_rule!(span in [kind, vars, content] = p.into_inner());
  Ok(Self { kind, vars, span: span.into(), content})
});

impl<'str, S: Display> Display for Quantifier<'str, S> {
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
