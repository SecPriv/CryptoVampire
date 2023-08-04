use itertools::Itertools;

use crate::formula::{formula::RichFormula, variable::Variable};

use super::substitution::Substitution;

#[derive(Debug, Clone)]
pub struct OwnedVarSubst<T> {
    pub field1: Vec<OneVarSubst<T>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub struct OneVarSubst<T> {
    pub id: usize,
    pub f: T,
}

pub type OwnedVarSubstF<'a, 'bump> = OwnedVarSubst<&'a RichFormula<'bump>>;
pub type OneVarSubstF<'a, 'bump> = OneVarSubst<&'a RichFormula<'bump>>;

impl<T> OneVarSubst<T> {
    pub fn id(&self) -> usize {
        self.id
    }

    pub fn f(&self) -> &T {
        &self.f
    }

    pub fn is_id(&self, id: usize) -> bool {
        self.id == id
    }
}
impl<T: Copy> OneVarSubst<T> {
    pub fn fc(&self) -> T {
        *self.f()
    }
}

impl<'bump, T> OwnedVarSubst<T> {
    pub fn get(&self, id: usize) -> Option<&T> {
        self.field1
            .iter()
            .find(|ovs| ovs.is_id(id))
            .map(|ovs| ovs.f())
    }

    pub fn new() -> Self {
        Self { field1: Vec::new() }
    }
}

impl<'bump, 'a> OwnedVarSubstF<'a, 'bump> {
    pub fn add(&mut self, id: usize, r: &'a RichFormula<'bump>) {
        debug_assert!(self.field1.iter().all(|ovs| ovs.is_id(id)));
        debug_assert!(match r {
            RichFormula::Var(v) => v.id != id,
            _ => true,
        });
        self.field1.push((id, r).into())
    }
}

impl<'a, 'bump> Substitution<'bump> for OwnedVarSubst<&'a RichFormula<'bump>>
where
    'bump: 'a,
{
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        self.field1
            .iter()
            .find(|ovs| ovs.is_id(var.id))
            // .map(|ovs| RichFormula::clone(*ovs.f()))
            .map(OneVarSubst::fc)
            .cloned()
            .unwrap_or(RichFormula::Var(var.clone()))
    }
}

impl<T> From<(usize, T)> for OneVarSubst<T> {
    fn from((id, f): (usize, T)) -> Self {
        Self { id, f }
    }
}

impl<T, U> FromIterator<U> for OwnedVarSubst<T>
where
    OneVarSubst<T> : From<U>
{
    fn from_iter<A: IntoIterator<Item = U>>(iter: A) -> Self {
        Self {
            field1: iter.into_iter().map_into().collect(),
        }
    }
}

impl<I, T, U> From<I> for OwnedVarSubst<T>
where
    I: IntoIterator<Item = U>,
    OneVarSubst<T> : From<U>
{
    fn from(value: I) -> Self {
        value.into_iter().collect()
    }
}

impl<T> Default for OwnedVarSubst<T> {
    fn default() -> Self {
        Self {
            field1: Default::default(),
        }
    }
}
