use pest::Span;

use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct LetIn<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub var: VariableBinding<L, S>,
    pub t1: Term<L, S>,
    pub t2: Term<L, S>,
}
boiler_plate!(LetIn<Span<'a>, &'a str>, 'a, let_in; |p| {
  let span = p.as_span().into();
  destruct_rule!(span in [var, t1, t2] = p.into_inner());
  Ok(Self { span, var, t1, t2})
});

impl<L, S: Display> Display for LetIn<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { var, t1, t2, .. } = self;
        write!(f, "let {var} = {t1} in {t2}")
    }
}
