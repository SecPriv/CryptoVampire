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

pub const OPERATION_LIST: [Operation; 7] = [
    Operation::HardEq,
    Operation::Eq,
    Operation::Neq,
    Operation::Or,
    Operation::And,
    Operation::Implies,
    Operation::Iff,
];

impl Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (*self).as_str().fmt(f)
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

impl Operation {
    pub fn get_operation(str: &str) -> Option<Self> {
        OPERATION_LIST
            .iter()
            .find(|x| x.as_str_alias().contains(&str))
            .cloned()
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Operation::HardEq => "===",
            Operation::Eq => "==",
            Operation::Neq => "!=",
            Operation::Or => "||",
            Operation::And => "&&",
            Operation::Implies => "=>",
            Operation::Iff => "<=>",
        }
    }

    /// Like [Operation::as_str] but taking into account some wide spread
    /// possible aliases.
    pub const fn as_str_alias(self) -> &'static [&'static str] {
        match self {
            Operation::HardEq => &["===", "meq"],
            Operation::Eq => &["=", "==", "eq"],
            Operation::Neq => &["!=", "neq", "<>"],
            Operation::Or => &["||", "or", "ors"],
            Operation::And => &["&&", "and", "ands"],
            Operation::Implies => &["=>", "implies", "==>"],
            Operation::Iff => &["<=>", "iff"],
        }
    }

    pub fn apply<'a, S>(self, args: implvec!(ast::Term<'a, S>)) -> ast::Term<'a, S> {
        Infix {
            span: Default::default(),
            operation: self,
            terms: args.into_iter().collect(),
        }
        .into()
    }
}
