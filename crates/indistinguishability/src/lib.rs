pub mod rules;

mod protocol;

mod terms {
  #[derive(Debug, Clone)]
  pub enum InnerFunction {
      And, Or, Implies, Not,
      Macro, Unfold, LT, Leq, Happens
  }

}