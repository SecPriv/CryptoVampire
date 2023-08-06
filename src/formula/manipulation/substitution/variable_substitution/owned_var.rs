use itertools::Itertools;

use crate::formula::variable::Variable;

use super::super::substitution::Substitution;

use crate::formula::formula::RichFormula;

use super::OneVarSubst;

#[derive(Debug, Clone)]
pub struct OwnedVarSubst<T> {
    pub subst: Vec<OneVarSubst<T>>,
}

pub type OwnedVarSubstF<'a, 'bump> = OwnedVarSubst<&'a RichFormula<'bump>>;

impl<'bump, T> OwnedVarSubst<T> {
    pub fn get(&self, id: usize) -> Option<&T> {
        self.subst
            .iter()
            .find(|ovs| ovs.is_id(id))
            .map(|ovs| ovs.f())
    }

    pub fn new() -> Self {
        Self { subst: Vec::new() }
    }
}

impl<'bump, 'a> OwnedVarSubstF<'a, 'bump> {
    pub fn add(&mut self, id: usize, r: &'a RichFormula<'bump>) {
        debug_assert!(self.subst.iter().all(|ovs| ovs.is_id(id)));
        debug_assert!(match r {
            RichFormula::Var(v) => v.id != id,
            _ => true,
        });
        self.subst.push((id, r).into())
    }
}

impl<T, U> FromIterator<U> for OwnedVarSubst<T>
where
    OneVarSubst<T>: From<U>,
{
    fn from_iter<A: IntoIterator<Item = U>>(iter: A) -> Self {
        Self {
            subst: iter.into_iter().map_into().collect(),
        }
    }
}

impl<I, T, U> From<I> for OwnedVarSubst<T>
where
    I: IntoIterator<Item = U>,
    OneVarSubst<T>: From<U>,
{
    fn from(value: I) -> Self {
        value.into_iter().collect()
    }
}

impl<T> Default for OwnedVarSubst<T> {
    fn default() -> Self {
        Self {
            subst: Default::default(),
        }
    }
}

impl<'a, 'bump> Substitution<'bump> for OwnedVarSubst<&'a RichFormula<'bump>>
where
    'bump: 'a,
{
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        self.subst
            .iter()
            .find(|ovs| ovs.is_id(var.id))
            // .map(|ovs| RichFormula::clone(*ovs.f()))
            .map(OneVarSubst::fc)
            .cloned()
            .unwrap_or(RichFormula::Var(var.clone()))
    }
}
