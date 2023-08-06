use itertools::Itertools;

use crate::{
    formula::{formula::RichFormula, manipulation::Substitution, variable::Variable},
    utils::vecref::VecRefClone,
};

use super::OneVarSubst;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FrozenOVSubst<'a, T: Clone> {
    content: VecRefClone<'a, OneVarSubst<T>>,
}

impl<'a, T: Clone> FrozenOVSubst<'a, T> {
    pub fn new<VRC: Into<VecRefClone<'a, OneVarSubst<T>>>>(content: VRC) -> Self {
        Self {
            content: content.into(),
        }
    }

    pub fn content(&self) -> &VecRefClone<'a, OneVarSubst<T>> {
        &self.content
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FrozenSubst<'a, T: Clone> {
    vars: VecRefClone<'a, usize>,
    formulas: VecRefClone<'a, T>,
}

impl<'a, T: Clone> FrozenSubst<'a, T> {
    pub fn new<VRCusize, VCRT>(var: VRCusize, formulas: VCRT) -> Self
    where
        VRCusize: Into<VecRefClone<'a, usize>>,
        VCRT: Into<VecRefClone<'a, T>>,
    {
        let r = Self {
            vars: var.into(),
            formulas: formulas.into(),
        };
        assert!(r.valid());
        r
    }
    pub fn vars(&self) -> &VecRefClone<'a, usize> {
        &self.vars
    }

    pub fn formulas(&self) -> &VecRefClone<'a, T> {
        &self.formulas
    }

    pub fn valid(&self) -> bool {
        self.vars.len() == self.formulas.len()
    }
}

impl<'a, T: Clone> Default for FrozenOVSubst<'a, T> {
    fn default() -> Self {
        Self {
            content: Default::default(),
        }
    }
}

impl<'a, T: Clone> Default for FrozenSubst<'a, T> {
    fn default() -> Self {
        Self {
            vars: Default::default(),
            formulas: Default::default(),
        }
    }
}

impl<'a, T: Clone> From<FrozenOVSubst<'a, T>> for FrozenSubst<'a, T> {
    fn from(value: FrozenOVSubst<'a, T>) -> Self {
        let (vars, formulas): (Vec<_>, Vec<_>) = value
            .content
            .into_iter()
            .map(|OneVarSubst { id, f }| (id, f))
            .unzip();
        Self::new(vars, formulas)
    }
}

impl<'a, T: Clone> From<FrozenSubst<'a, T>> for FrozenOVSubst<'a, T> {
    fn from(FrozenSubst { vars, formulas }: FrozenSubst<'a, T>) -> Self {
        // let FrozenSubst { vars, formulas } = value;
        // assert_eq!(vars.len(), formulas.len());
        let content: Vec<OneVarSubst<_>> = vars
            .into_iter()
            .zip_eq(formulas.into_iter())
            .map_into()
            .collect_vec();
        Self::new(content)
    }
}

impl<'a, 'bump: 'a> Substitution<'bump> for FrozenOVSubst<'a, RichFormula<'bump>> {
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        self.content()
            .into_iter()
            .find(|ovs| ovs.id() == var.id)
            .map(|ovs| ovs.as_ref().get(var))
            .unwrap_or(RichFormula::Var(*var))
    }
}

impl<'a, 'bump: 'a> Substitution<'bump> for FrozenSubst<'a, RichFormula<'bump>> {
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        let FrozenSubst { vars, formulas, .. } = self;
        vars.iter()
            .zip_eq(formulas.iter())
            .find(|(&id, _)| id == var.id)
            .map(|(_, f)| f.clone())
            .unwrap_or(RichFormula::Var(*var))
    }
}
