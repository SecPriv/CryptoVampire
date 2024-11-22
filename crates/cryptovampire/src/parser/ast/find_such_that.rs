use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FindSuchThat<'str, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: ASTLocation<'str>,
    pub vars: TypedArgument<'str, S>,
    pub condition: Term<'str, S>,
    pub left: Term<'str, S>,
    pub right: Term<'str, S>,
}
boiler_plate!(@ FindSuchThat, 'a, find_such_that; |p| {
  let span = p.as_span();
  destruct_rule!(span in [vars, condition, left, right] = p.into_inner());
  Ok(Self { span:span.into(), vars, condition, left, right})
});

impl<'str, S: Display> Display for FindSuchThat<'str, S> {
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
