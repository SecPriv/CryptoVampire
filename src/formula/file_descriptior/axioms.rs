use crate::formula::{formula::RichFormula, function::Function, variable::Variable};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Axiom<'bump> {
    Base { formula: Box<RichFormula<'bump>> },
    Theory { formula: Box<RichFormula<'bump>> },
    Query { formula: Box<RichFormula<'bump>> },
    Rewrite { rewrite: Box<Rewrite<'bump>> },
}

impl<'bump> Axiom<'bump> {
    pub fn base(f: RichFormula<'bump>) -> Self {
        Self::Base {
            formula: Box::new(f),
        }
    }
    pub fn theory(f: RichFormula<'bump>) -> Self {
        Self::Theory {
            formula: Box::new(f),
        }
    }
    pub fn query(f: RichFormula<'bump>) -> Self {
        Self::Query {
            formula: Box::new(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rewrite<'bump> {
    pub kind: RewriteKind,
    pub function: Function<'bump>,
    pub vars: Vec<Variable<'bump>>,
    pub pre: RichFormula<'bump>,
    pub post: RichFormula<'bump>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RewriteKind {
    Bool,
    Other,
}
