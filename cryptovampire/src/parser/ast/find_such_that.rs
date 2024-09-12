use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FindSuchThat<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub vars: TypedArgument<'a, S>,
    pub condition: Term<'a, S>,
    pub left: Term<'a, S>,
    pub right: Term<'a, S>,
}
boiler_plate!(FindSuchThat<'a>, 'a, find_such_that; |p| {
  let span = p.as_span().into();
  destruct_rule!(span in [vars, condition, left, right] = p.into_inner());
  Ok(Self { vars, span, condition, left, right})
});

impl<'a, S: Display> Display for FindSuchThat<'a, S> {
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
