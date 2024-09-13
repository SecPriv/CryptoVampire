use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct IfThenElse<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub condition: Term<L, S>,
    pub left: Term<L, S>,
    pub right: Term<L, S>,
}
boiler_plate!(@ IfThenElse, 'a, if_then_else; |p| {
  let span = p.as_span();
  destruct_rule!(span in [condition, left, right] = p.into_inner());
  Ok(IfThenElse { span, condition, left, right})
});

impl<L, S: Display> Display for IfThenElse<L, S> {
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
