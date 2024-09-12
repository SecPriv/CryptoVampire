use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct IfThenElse<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub condition: Term<'a, S>,
    pub left: Term<'a, S>,
    pub right: Term<'a, S>,
}
boiler_plate!(IfThenElse<'a>, 'a, if_then_else; |p| {
  let span = p.as_span().into();
  destruct_rule!(span in [condition, left, right] = p.into_inner());
  Ok(IfThenElse { span, condition, left, right})
});

impl<'a, S: Display> Display for IfThenElse<'a, S> {
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
