use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FindSuchThat<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub vars: TypedArgument<L, S>,
    pub condition: Term<L, S>,
    pub left: Term<L, S>,
    pub right: Term<L, S>,
}
boiler_plate!(@ FindSuchThat, 'a, find_such_that; |p| {
  let span = p.as_span().into();
  destruct_rule!(span in [vars, condition, left, right] = p.into_inner());
  Ok(Self { vars, span, condition, left, right})
});

impl<'a, L, S: Display> Display for FindSuchThat<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            vars,
            condition,
            left,
            right,
            ..
        } = self;
        write!(
            f,
            "try find {vars}\nsuch that {{{condition}}}\nthen {{{left}}}\nelse {{{right}}}"
        )
    }
}
