use std::{default, fmt::Display, rc::Rc};

use egg::{Analysis, Id, Language};

use crate::{Program, Rule};

#[derive(Clone)]
pub struct ProofItem<L: Language, N: Analysis<L>> {
    pub rule: Rc<dyn Rule<L, N>>,
    pub ids: Vec<Id>,
    pub side_condition: Option<Rc<dyn Display>>,
}

#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SearchResult {
    #[default]
    False,
    True(Id),
}

impl SearchResult {
    pub fn as_bool(&self) -> bool {
        matches!(self, Self::True(_))
    }
}

#[allow(dead_code)]
pub struct Proof<'a, L: Language, N: Analysis<L>> {
  prog: &'a Program<L, N>,
  id: Id
}
