use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Infix<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub operation: Operation,
    pub terms: Vec<Term<'a, S>>,
}
boiler_plate!(Infix<'a>, 'a, infix_term; |p| {
  let span = p.as_span().into();
  let mut terms = Vec::new();

  let mut p = p.into_inner();

  terms.push(p.next().unwrap().try_into()?);
  let operation : Operation = p.next().unwrap().try_into()?;
  terms.push(p.next().unwrap().try_into()?);

  while let Some(n_op) = p.next() {
      let n_op_span = n_op.as_span();
      if operation != Operation::try_from(n_op)? {
          bail_at!(n_op_span, "should be {}", operation)
      }
      terms.push(p.next().unwrap().try_into()?)
  }
  Ok(Infix { span, operation, terms })
});

impl<'a, S: Display> Display for Infix<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let op = format!(" {} ", &self.operation);
        write!(f, "({})", self.terms.iter().format(&op))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Operation {
    HardEq,
    Eq,
    Neq,
    Or,
    And,
    Implies,
    Iff,
}

impl Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operation::HardEq => "===",
            Operation::Eq => "==",
            Operation::Neq => "!=",
            Operation::Or => "||",
            Operation::And => "&&",
            Operation::Implies => "=>",
            Operation::Iff => "<=>",
        }
        .fmt(f)
    }
}

boiler_plate!(Operation, operation; {
  hard_eq => HardEq,
  eq => Eq,
  neq => Neq,
  or => Or,
  and => And,
  implies => Implies,
  iff => Iff
});
