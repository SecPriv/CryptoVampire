use std::{
    borrow::Borrow,
    fmt::Display,
    ops::{BitAnd, BitOr, Deref, DerefMut, Not, Shr},
};

use crate::formula::utils::Applicable;
use crate::formula::{
    function::builtin::{AND, IMPLIES, NOT, OR, TRUE_ARC},
    utils::formula_iterator::{FormulaIterator, IteratorFlags},
    variable::{IntoVariableIter, Variable},
};

use super::RichFormula;
use utils::{
    arc_into_iter::ArcIntoIter,
    utils::{repeat_n_zip, MaybeInvalid, StackBox},
    vecref::VecRefClone,
};

use std::sync::Arc;

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

    pub fn used_variables_iter(&self) -> impl Iterator<Item = Variable<'bump>> {
        self.used_variables_iter_with_pile(StackBox::new(Vec::with_capacity(1)))
    }

    pub fn used_variables_iter_with_pile<V>(
        &self,
        mut pile: V,
    ) -> impl Iterator<Item = Variable<'bump>>
    where
        V: DerefMut<Target = Vec<((), Self)>> + Deref<Target = Vec<((), Self)>>,
    {
        pile.clear();
        pile.push(((), self.clone()));
        FormulaIterator {
            pile,
            passed_along: None,
            flags: IteratorFlags::QUANTIFIER,
            f: |_, f| {
                let (v, n) = match f.as_ref() {
                    RichFormula::Fun(fun, args) => {
                        let bvars = fun
                            .as_quantifer()
                            .map(|q| VecRefClone::Vec(Arc::clone(&q.bound_variables)));
                        (bvars, VecRefClone::Vec(Arc::clone(&args)))
                    }
                    RichFormula::Var(v) => (Some(VecRefClone::Owned(*v)), Default::default()),
                    _ => (None, Default::default()),
                };
                (v, repeat_n_zip((), n))
            },
        }
        .flat_map(|iv| iv.into_iter())
    }

    pub fn iter_with_pile<V>(&self, mut pile: V) -> impl Iterator<Item = ARichFormula<'bump>>
    where
        V: DerefMut<Target = Vec<((), Self)>> + Deref<Target = Vec<((), Self)>>,
    {
        pile.clear();
        pile.push(((), self.clone()));
        FormulaIterator {
            pile,
            passed_along: None,
            flags: IteratorFlags::QUANTIFIER,
            f: |_, f| {
                let next = match f.as_ref() {
                    RichFormula::Fun(_, args) => Some(ArcIntoIter::from(args)),
                    _ => None,
                };
                (Some(f), repeat_n_zip((), next.into_iter().flatten()))
            },
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = ARichFormula<'bump>> {
        self.iter_with_pile(StackBox::new(vec![]))
    }

    pub fn iter_used_varibales_with_pile<'a, V, D>(
        mut pile: V,
        fs: impl IntoIterator<Item = Self>,
    ) -> impl Iterator<Item = Variable<'bump>> + 'a
    where
        V: DerefMut<Target = Vec<(D, Self)>> + Deref<Target = Vec<(D, Self)>> + 'a,
        D: Default + Clone + 'a,
        'bump: 'a,
    {
        pile.clear();
        pile.extend(fs.into_iter().map(|f| (Default::default(), f)));
        FormulaIterator {
            pile,
            passed_along: None,
            flags: IteratorFlags::QUANTIFIER,
            f: |_, f| {
                let (current, next) = match f.as_ref() {
                    RichFormula::Var(v) => (Some(*v), None),
                    RichFormula::Fun(_, args) => (None, Some(ArcIntoIter::from(args))),
                    _ => (None, None),
                };
                (
                    current,
                    next.into_iter().flatten().map(|f| (Default::default(), f)),
                )
            },
        }
    }

    pub fn iter_used_varibales<'a>(
        fs: impl IntoIterator<Item = Self>,
    ) -> impl Iterator<Item = Variable<'bump>> + 'a
    where
        'bump: 'a,
    {
        Self::iter_used_varibales_with_pile(StackBox::new(Vec::<((), _)>::new()), fs)
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
            panic!("The formula contains some uninitialized bit. This should not happen please report it")
        }
    }
}

impl<'a, 'bump> IntoVariableIter<'bump> for &'a ARichFormula<'bump> {
    fn vars_iter(self) -> impl Iterator<Item = Variable<'bump>> {
        self.used_variables_iter()
    }
}

impl<'bump> IntoVariableIter<'bump> for ARichFormula<'bump> {
    fn vars_iter(self) -> impl Iterator<Item = Variable<'bump>> {
        self.used_variables_iter()
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
