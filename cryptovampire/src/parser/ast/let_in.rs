use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct LetIn<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub var: Variable<'a, S>,
    pub t1: Term<'a, S>,
    pub t2: Term<'a, S>,
}
boiler_plate!(LetIn<'a>, 'a, let_in; |p| {
  let span = p.as_span().into();
  destruct_rule!(span in [var, t1, t2] = p.into_inner());
  Ok(Self { span, var, t1, t2})
});

impl<'a, S: Display> Display for LetIn<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { var, t1, t2, .. } = self;
        write!(f, "let {var} = {t1} in {t2}")
    }
}
