use utils::string_ref::StrRef;

use crate::environement::traits::{KnowsRealm, Realm};
use crate::formula::sort::{Sort, new_idx};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum UserEvaluatable<'bump> {
    Symbolic {
        name: Box<str>,
        eval: Sort<'bump>,
        id: u8,
    },
    Evaluated {
        symbolic: Sort<'bump>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Index {
    name: Box<str>,
    pub(crate) id: u8,
}

impl<'bump> UserEvaluatable<'bump> {
    pub fn name(&self) -> StrRef<'_> {
        match self {
            UserEvaluatable::Symbolic { name, .. } => name.as_ref().into(),
            UserEvaluatable::Evaluated { symbolic } => format!("eval${}", symbolic.name()).into(),
        }
    }

    /// Returns `true` if the user evaluatable is [`Evaluated`].
    ///
    /// [`Evaluated`]: UserEvaluatable::Evaluated
    #[must_use]
    pub fn is_evaluated(&self) -> bool {
        matches!(self, Self::Evaluated { .. })
    }

    /// Returns `true` if the user evaluatable is [`Symbolic`].
    ///
    /// [`Symbolic`]: UserEvaluatable::Symbolic
    #[must_use]
    pub fn is_symbolic(&self) -> bool {
        matches!(self, Self::Symbolic { .. })
    }

    pub fn evaluated_sort(&self) -> Option<Sort<'bump>> {
        match self {
            UserEvaluatable::Symbolic { eval, .. } => Some(*eval),
            _ => None,
        }
    }
}

impl Index {
    pub fn new(name: Box<str>) -> Self {
        Self {
            name,
            id: new_idx(),
        }
    }

    pub fn name(&self) -> StrRef<'_> {
        self.name.as_ref().into()
    }
}

impl<'bump> KnowsRealm for UserEvaluatable<'bump> {
    fn get_realm(&self) -> Realm {
        match self {
            UserEvaluatable::Symbolic { .. } => Realm::Symbolic,
            UserEvaluatable::Evaluated { .. } => Realm::Evaluated,
        }
    }
}
