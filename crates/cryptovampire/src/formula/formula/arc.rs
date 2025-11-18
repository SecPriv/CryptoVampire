use std::borrow::Borrow;
use std::fmt::Display;
use std::ops::{BitAnd, BitOr, Deref, Not, Shr};
use std::sync::Arc;

use itertools::Either;
use logic_formula::{AsFormula, Destructed, Head};
use utils::arc_into_iter::ArcIntoIter;
use utils::utils::MaybeInvalid;

use super::{Expander, RichFormula};
use crate::formula::function::Function;
use crate::formula::function::builtin::{AND, IMPLIES, NOT, OR, TRUE_ARC};
use crate::formula::quantifier::Quantifier;
use crate::formula::utils::Applicable;
use crate::formula::variable::{IntoVariableIter, Variable};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ARichFormula<'bump>(Arc<RichFormula<'bump>>);

impl<'bump> From<RichFormula<'bump>> for ARichFormula<'bump> {
    fn from(value: RichFormula<'bump>) -> Self {
        Self(Arc::new(value))
    }
}

impl<'a, 'bump: 'a> From<&'a RichFormula<'bump>> for ARichFormula<'bump> {
    fn from(value: &'a RichFormula<'bump>) -> Self {
        value.clone().into()
    }
}

impl<'bump> From<Variable<'bump>> for ARichFormula<'bump> {
    fn from(value: Variable<'bump>) -> Self {
        Self(Arc::new(RichFormula::Var(value)))
    }
}

impl<'a, 'bump: 'a> From<&'a Variable<'bump>> for ARichFormula<'bump> {
    fn from(value: &'a Variable<'bump>) -> Self {
        Self(Arc::new(RichFormula::Var(*value)))
    }
}

impl<'a, 'bump: 'a> From<&'a ARichFormula<'bump>> for ARichFormula<'bump> {
    fn from(value: &'a ARichFormula<'bump>) -> Self {
        value.shallow_copy()
    }
}

impl<'bump> Deref for ARichFormula<'bump> {
    type Target = RichFormula<'bump>;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'bump> AsRef<RichFormula<'bump>> for ARichFormula<'bump> {
    fn as_ref(&self) -> &RichFormula<'bump> {
        self.0.as_ref()
    }
}

impl<'bump> Borrow<RichFormula<'bump>> for ARichFormula<'bump> {
    fn borrow(&self) -> &RichFormula<'bump> {
        self.as_ref()
    }
}

impl<'bump> ARichFormula<'bump> {
    /// Returns the shallow copy of this [`ARichFormula`].
    pub fn shallow_copy(&self) -> Self {
        Self(Arc::clone(self.as_arc()))
    }

    pub fn as_arc(&self) -> &Arc<RichFormula<'bump>> {
        &self.0
    }

    pub fn as_inner(&self) -> &RichFormula<'bump> {
        self.as_ref()
    }

    /// Clone the inner [RichFormula] and returns it
    ///
    /// Favor [Self::owned_into_inner()]
    pub fn into_inner(&self) -> RichFormula<'bump> {
        self.as_inner().clone()
    }

    /// tries to move out of the [Arc], clones otherwise
    pub fn owned_into_inner(self) -> RichFormula<'bump> {
        if Arc::strong_count(&self.0) <= 1 {
            // we are the only one using the Arc
            Arc::into_inner(self.0).unwrap() // can't fail
        } else {
            self.into_inner()
        }
    }

    pub fn as_expander<'a>(&'a self) -> Expander<'a, 'bump> {
        self.into()
    }
}

impl<'bump> BitAnd for ARichFormula<'bump> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        AND.f([self, rhs])
    }
}

impl<'bump> BitOr for ARichFormula<'bump> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        OR.f([self, rhs])
    }
}

impl<'bump> Not for ARichFormula<'bump> {
    type Output = Self;

    fn not(self) -> Self::Output {
        NOT.f([self])
    }
}

impl<'bump> Shr for ARichFormula<'bump> {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        IMPLIES.f([self, rhs])
    }
}

impl<'bump> Display for ARichFormula<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_valid() {
            write!(f, "{}", self.as_inner())
        } else if cfg!(debug_assertions) {
            write!(f, "(unintialized formula) {:?}", self.as_inner())
        } else {
            panic!(
                "The formula contains some uninitialized bit. This should not happen please \
                 report it"
            )
        }
    }
}

impl<'a, 'bump> IntoVariableIter<'bump> for &'a ARichFormula<'bump> {
    fn vars_iter(self) -> impl Iterator<Item = Variable<'bump>> {
        self.as_expander().used_vars_iter()
    }
}

impl<'bump> Default for ARichFormula<'bump> {
    fn default() -> Self {
        TRUE_ARC.clone()
    }
}

impl<'bump> MaybeInvalid for ARichFormula<'bump> {
    fn is_valid(&self) -> bool {
        RichFormula::is_valid(self.as_ref())
    }
}

impl<'a, 'bump> logic_formula::AsFormula for &'a ARichFormula<'bump> {
    type Var = Variable<'bump>;

    type Fun = Function<'bump>;

    type Quant = Quantifier<'bump>;

    fn destruct(self) -> logic_formula::Destructed<Self, impl Iterator<Item = Self>> {
        match self.as_ref() {
            RichFormula::Var(v) => Destructed {
                head: Head::<&'a ARichFormula<'bump>>::Var(*v),
                args: Either::Left(std::iter::empty()),
            },
            RichFormula::Fun(f, args) => Destructed {
                head: Head::<&'a ARichFormula<'bump>>::Fun(*f),
                args: Either::Right(Either::Left(args.as_ref().iter())),
            },
            RichFormula::Quantifier(q, arg) => Destructed {
                head: Head::<&'a ARichFormula<'bump>>::Quant(q.clone()),
                args: Either::Right(Either::Right([arg].into_iter())),
            },
        }
    }
}

impl<'bump> logic_formula::AsFormula for ARichFormula<'bump> {
    type Var = Variable<'bump>;

    type Fun = Function<'bump>;

    type Quant = Quantifier<'bump>;

    fn destruct(self) -> logic_formula::Destructed<Self, impl Iterator<Item = Self>> {
        match self.as_ref() {
            RichFormula::Var(v) => Destructed {
                head: Head::<ARichFormula<'bump>>::Var(*v),
                args: Either::Left(ArcIntoIter::empty()),
            },
            RichFormula::Fun(f, args) => Destructed {
                head: Head::<ARichFormula<'bump>>::Fun(*f),
                args: Either::Left(ArcIntoIter::from(args)),
            },
            RichFormula::Quantifier(q, arg) => Destructed {
                head: Head::<ARichFormula<'bump>>::Quant(q.clone()),
                args: Either::Right([arg.shallow_copy()].into_iter()),
            },
        }
    }
}

impl<'a, 'bump> crate::error::LocationProvider for &'a ARichFormula<'bump> {
    fn provide(self) -> crate::error::Location {
        crate::error::Location::from_display(self)
    }
}
