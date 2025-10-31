// use core::slice::SlicePattern;

use std::fmt::Display;
use std::sync::Arc;

use itertools::Itertools;
use logic_formula::Bounder;
use utils::implvec;

use super::sort::Sort;
use super::sort::builtins::BOOL;
use super::variable::Variable;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Quantifier<'bump> {
    Exists {
        // status: Status,
        variables: Arc<[Variable<'bump>]>,
    },
    Forall {
        // status: Status,
        variables: Arc<[Variable<'bump>]>,
    },
    // FindSuchThat { variables: Vec<Variable<'bump>> },
}

impl<'bump> Quantifier<'bump> {
    pub fn get_output_sort(&self) -> Sort<'bump> {
        BOOL.as_sort()
    }

    /// the variables bound by the quantifier
    pub fn get_variables(&self) -> &Arc<[Variable<'bump>]> {
        match self {
            Quantifier::Exists { variables, .. } | Quantifier::Forall { variables, .. } => {
                variables
            }
        }
    }

    pub fn exists(variables: implvec!(Variable<'bump>)) -> Self {
        Self::Exists {
            variables: variables.into_iter().collect(),
        }
    }

    pub fn forall(variables: implvec!(Variable<'bump>)) -> Self {
        Self::Forall {
            variables: variables.into_iter().collect(),
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            Quantifier::Exists { .. } => "exist",
            Quantifier::Forall { .. } => "forall",
        }
    }
}

impl<'bump> Display for Quantifier<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vars = self.get_variables().iter().join(",");
        match self {
            Self::Exists { .. } => write!(f, "∃({}). ", vars),
            Self::Forall { .. } => write!(f, "∀({}). ", vars),
        }
    }
}

impl<'bump> Bounder<Variable<'bump>> for Quantifier<'bump> {
    fn bounds(&self) -> impl Iterator<Item = Variable<'bump>> {
        match self {
            Quantifier::Exists { variables } | Quantifier::Forall { variables } => {
                variables.iter().cloned()
            }
        }
    }
}

fn _enlarge<'a, 'b>(q: Quantifier<'a>) -> Quantifier<'b>
where
    'a: 'b,
{
    q
}
