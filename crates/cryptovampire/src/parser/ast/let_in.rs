use cryptovampire_macros::LocationProvider;
use location::ASTLocation;
use pest::Span;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct LetIn<'str, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: ASTLocation<'str>,
    pub var: VariableBinding<'str, S>,
    pub t1: Term<'str, S>,
    pub t2: Term<'str, S>,
}
boiler_plate!(LetIn<'a, &'a str>, 'a, let_in; |p| {
  let span = p.as_span().into();
  destruct_rule!(span in [var, t1, t2] = p.into_inner());
  Ok(Self { span, var, t1, t2})
});

impl<'str, S: Display> Display for LetIn<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { var, t1, t2, .. } = self;
        write!(f, "let {var} = {t1} in {t2}")
    }
}
