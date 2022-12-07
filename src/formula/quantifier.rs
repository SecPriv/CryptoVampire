use super::formula::Variable;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Quantifier {
    Exists { variable: Vec<Variable> },
    Forall { variable: Vec<Variable> },
    FindSuchThat { variable: Vec<Variable> },
}
