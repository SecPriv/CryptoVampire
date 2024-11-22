use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct IfThenElse<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub condition: Term<'str, S>,
    pub left: Term<'str, S>,
    pub right: Term<'str, S>,
}
boiler_plate!(@ IfThenElse, 'a, if_then_else; |p| {
  let span = p.as_span();
  destruct_rule!(span in [condition, left, right] = p.into_inner());
  Ok(IfThenElse { span: span.into(), condition, left, right})
});

impl<'str, S: Display> Display for IfThenElse<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            condition,
            left,
            right,
            ..
        } = self;
        write!(f, "if {condition}\n{{\n\t{left}\n}} else {{\n\t{right}\n}}")
    }
}
