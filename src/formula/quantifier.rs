use super::{
    builtins::types::{BOOL, MSG},
    formula::Variable,
    sort::Sort,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Quantifier {
    Exists { variables: Vec<Variable> },
    Forall { variables: Vec<Variable> },
    FindSuchThat { variables: Vec<Variable> },
}

impl Quantifier {
    pub fn get_output_sort(&self) -> &Sort {
        match self {
            Quantifier::Exists { variables: _ } => &BOOL,
            Quantifier::Forall { variables: _ } => &BOOL,
            Quantifier::FindSuchThat { variables: _ } => &MSG,
        }
    }

    pub fn get_variables(&self) -> &[Variable] {
        match self {
            Quantifier::Exists { variables: variable } => variable.as_slice(),
            Quantifier::Forall { variables: variable } => variable.as_slice(),
            Quantifier::FindSuchThat { variables: variable } => variable.as_slice(),
        }
    }
}
