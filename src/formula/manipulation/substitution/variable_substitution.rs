
use crate::formula::{formula::RichFormula, variable::Variable};

use super::substitution::Substitution;


#[derive(Debug, Clone)]
pub struct OwnedVarSubst<T> { pub field1: Vec<(usize, T)> }

impl<'bump, T> OwnedVarSubst<T> {
    pub fn get(&self, id: usize) -> Option<&T> {
        self.field1.iter().find(|(i, _)| i == &id).map(|(_, f)| f)
    }

    pub fn new() -> Self {
        Self{ field1: Vec::new()}
    }
}

impl<'bump, 'a> OwnedVarSubst<&'a RichFormula<'bump>> {
    pub fn add(&mut self, id: usize, r: &'a RichFormula<'bump>) {
        debug_assert!(self.field1.iter().all(|(i, _)| i != &id));
        debug_assert!(match r {
            RichFormula::Var(v) => v.id != id,
            _ => true,
        });
        self.field1.push((id, r))
    }
}


impl<'a, 'bump> Substitution<'bump> for OwnedVarSubst<&'a RichFormula<'bump>>
where
    'bump: 'a,
{
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        self.field1
            .iter()
            .find(|(nid, _)| nid == &var.id)
            .map(|(_, f)| RichFormula::clone(f))
            .unwrap_or(RichFormula::Var(var.clone()))
    }
}