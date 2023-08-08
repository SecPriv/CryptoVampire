use crate::formula::{
    formula::{ARichFormula, RichFormula},
    manipulation::Substitution,
    variable::Variable,
};

use super::OwnedVarSubst;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub struct OneVarSubst<T> {
    pub id: usize,
    pub f: T,
}

pub type OneVarSubstF<'bump> = OneVarSubst<ARichFormula<'bump>>;

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

impl<T: Clone> OneVarSubst<T> {
    pub fn fc(&self) -> T {
        self.f().clone()
    }
}

impl<T> From<(usize, T)> for OneVarSubst<T> {
    fn from((id, f): (usize, T)) -> Self {
        Self { id, f }
    }
}

impl<'a, 'bump: 'a> Substitution<'bump> for OneVarSubstF<'bump> {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        if var.id == self.id {
            self.f.clone()
        } else {
            RichFormula::from(*var).into()
        }
    }
}
