use super::{
    builtins::types::{BOOL, MSG},
    formula::Variable,
    sort::Sort,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Quantifier {
    Exists { variable: Vec<Variable> },
    Forall { variable: Vec<Variable> },
    FindSuchThat { variable: Vec<Variable> },
}

impl Quantifier {
    pub fn get_output_sort(&self) -> &Sort {
        match self {
            Quantifier::Exists { variable: _ } => &BOOL,
            Quantifier::Forall { variable: _ } => &BOOL,
            Quantifier::FindSuchThat { variable: _ } => &MSG,
        }
    }

    pub fn get_variables(&self) -> &[Variable] {
        match self {
            Quantifier::Exists { variable } => variable.as_slice(),
            Quantifier::Forall { variable } => variable.as_slice(),
            Quantifier::FindSuchThat { variable } => variable.as_slice(),
        }
    }
}
