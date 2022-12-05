pub enum Formula<F> {
    Var(String),
    Fun(F, Vec<Formula>),
    Qnt(Quantifier, String, Box<Formula>)
}