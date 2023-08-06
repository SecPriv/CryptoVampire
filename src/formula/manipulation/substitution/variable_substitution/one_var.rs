use crate::formula::{formula::RichFormula, manipulation::Substitution, variable::Variable};

use super::OwnedVarSubst;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub struct OneVarSubst<T> {
    pub id: usize,
    pub f: T,
}

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

    pub fn add<U>(self, value: U) -> OwnedVarSubst<T>
    where
        Self: From<U>,
    {
        [self, value.into()].into()
    }

    pub fn as_ref(&self) -> OneVarSubst<&'_ T> {
        let OneVarSubst { id, f } = self;
        OneVarSubst { id: *id, f }
    }
}

impl<T: Copy> OneVarSubst<T> {
    pub fn fc(&self) -> T {
        *self.f()
    }
}

impl<T> From<(usize, T)> for OneVarSubst<T> {
    fn from((id, f): (usize, T)) -> Self {
        Self { id, f }
    }
}

impl<'a, 'bump:'a> Substitution<'bump> for OneVarSubstF<'a, 'bump> {
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        if var.id == self.id {
            self.f.clone()
        } else {
            RichFormula::from(*var)
        }
    }
}