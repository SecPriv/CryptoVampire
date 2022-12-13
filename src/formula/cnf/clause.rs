use std::{collections::HashSet, ops::Add};

use crate::formula::formula::Variable;

use super::litteral::Litteral;
use bitflags::bitflags;

bitflags! {
    #[derive(Default)]
    struct Flags: u32 {
        const ORDERED =       0b00001;
        const DELETED =       0b00010;
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Clause {
    litterals: Vec<Litteral>,
    flags: Flags,
    // parents: Vec<Arc<Self>>
}

impl Default for Clause {
    fn default() -> Self {
        Self {
            litterals: Default::default(),
            flags: Default::default(),
        }
    }
}

impl Clause {
    pub fn new(l: Vec<Litteral>) -> Self {
        Clause {
            litterals: l,
            ..Default::default()
        }
    }

    pub fn is_ordered(&self) -> bool {
        self.flags.contains(Flags::ORDERED)
    }

    pub fn order(&mut self) {
        if !self.is_ordered() {
            self.litterals.sort();
            self.flags |= Flags::ORDERED
        }
    }

    pub fn litterals(&self) -> &Vec<Litteral> {
        &self.litterals
    }

    pub fn litterals_mut(&mut self) -> &mut Vec<Litteral> {
        self.flags.remove(Flags::ORDERED);
        &mut self.litterals
    }

    pub fn variables_iter(&self) -> impl Iterator<Item = &Variable> {
        self.litterals.iter().flat_map(Litteral::variables_iter)
    }

    // I assume there shouldn't be that many variables per clauses, so this should be the fastest
    pub fn variables_unique(&self) -> Vec<Variable> {
        let mut vec = Vec::new();
        for v in self.variables_iter() {
            if !vec.contains(v) {
                vec.push(v.clone())
            }
        }
        vec
    }

    pub fn variables_unique_big(&self) -> HashSet<Variable> {
        self.variables_iter().map(|v| v.clone()).collect()
    }
}

impl Add for &Clause {
    type Output = Clause;

    fn add(self, rhs: Self) -> Self::Output {
        Clause::new(
            self.litterals()
                .iter()
                .chain(rhs.litterals().iter())
                .map(|f| f.clone())
                .collect(),
        )
    }
}

impl FromIterator<Litteral> for Clause {
    fn from_iter<T: IntoIterator<Item = Litteral>>(iter: T) -> Self {
        Self::new(iter.into_iter().collect())
    }
}
