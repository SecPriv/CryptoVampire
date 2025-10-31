use itertools::Itertools;

use super::super::substitution::Substitution;
use super::OneVarSubst;
use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::variable::{Variable, uvar};

/// List of [OneVarSubst], to more easily deal with the substitution of mulitple variables.
///
/// Note that this is *not* the same as chaining [OneVarSubst]s as only the first matching substitution is applied.
///
/// ### Invariants
/// There should be no two duplicates in the list. That is, no variables should points to two different terms
#[derive(Debug, Clone)]
pub struct MultipleVarSubst<T> {
    subst: Vec<OneVarSubst<T>>,
}

pub type MulitpleVarSubstF<'bump> = MultipleVarSubst<ARichFormula<'bump>>;

impl<T> MultipleVarSubst<T> {
    pub fn maybe_get(&self, id: uvar) -> Option<&T> {
        self.subst
            .iter()
            .find(|ovs| ovs.is_id(id))
            .map(|ovs| ovs.f())
    }

    pub fn new() -> Self {
        Self { subst: Vec::new() }
    }

    pub fn subst(&self) -> &[OneVarSubst<T>] {
        &self.subst
    }
}

impl<'bump> MulitpleVarSubstF<'bump> {
    /// add a substitution to the list such that the variable number `id` will be replaced by `r`
    ///
    /// In debug mode, it checks that the invariant is held.
    pub fn add(&mut self, id: uvar, r: ARichFormula<'bump>) {
        debug_assert!(self.subst.iter().all(|ovs| !ovs.is_id(id)));
        debug_assert!(match r.as_ref() {
            RichFormula::Var(v) => v.id != id,
            _ => true,
        });
        self.subst.push((id, r).into())
    }

    pub fn maybe_get_as_rf(&self, id: uvar) -> Option<&RichFormula<'bump>> {
        self.maybe_get(id).map(ARichFormula::as_ref)
    }
}

impl<T, U> FromIterator<U> for MultipleVarSubst<T>
where
    OneVarSubst<T>: From<U>,
{
    fn from_iter<A: IntoIterator<Item = U>>(iter: A) -> Self {
        Self {
            subst: iter.into_iter().map_into().collect(),
        }
    }
}

impl<I, T, U> From<I> for MultipleVarSubst<T>
where
    I: IntoIterator<Item = U>,
    OneVarSubst<T>: From<U>,
{
    fn from(value: I) -> Self {
        value.into_iter().collect()
    }
}

impl<T> Default for MultipleVarSubst<T> {
    fn default() -> Self {
        Self {
            subst: Default::default(),
        }
    }
}

impl<'a, 'bump> Substitution<'bump> for MultipleVarSubst<ARichFormula<'bump>>
where
    'bump: 'a,
{
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        self.maybe_get(var.id)
            .cloned()
            .unwrap_or_else(|| RichFormula::Var(*var).into())
    }
}
