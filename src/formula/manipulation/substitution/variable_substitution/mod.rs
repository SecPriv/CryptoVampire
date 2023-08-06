use itertools::Itertools;

use crate::formula::{formula::RichFormula, variable::Variable};

use super::substitution::Substitution;

pub use one_var::{OneVarSubst, OneVarSubstF};
mod one_var;

pub use owned_var::{OwnedVarSubst, OwnedVarSubstF};

mod owned_var;
mod ref_substitution;