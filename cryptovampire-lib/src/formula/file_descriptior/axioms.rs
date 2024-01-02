use std::sync::Arc;

use crate::formula::{formula::ARichFormula, function::Function, sort::Sort, variable::Variable};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Axiom<'bump> {
    Comment(Box<str>),
    Base {
        formula: ARichFormula<'bump>,
    },
    Ground {
        sort: Sort<'bump>,
        formula: ARichFormula<'bump>,
    },
    Theory {
        formula: ARichFormula<'bump>,
    },
    Query {
        formula: ARichFormula<'bump>,
    },
    Rewrite {
        rewrite: Box<Rewrite<'bump>>,
    },
}

impl<'bump> Axiom<'bump> {
    pub fn base(f: ARichFormula<'bump>) -> Self {
        Self::Base { formula: f }
    }
    pub fn theory(f: ARichFormula<'bump>) -> Self {
        Self::Theory { formula: f }
    }
    pub fn query(f: ARichFormula<'bump>) -> Self {
        Self::Query { formula: f }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rewrite<'bump> {
    pub kind: RewriteKind<'bump>,
    pub vars: Arc<[Variable<'bump>]>,
    pub pre: ARichFormula<'bump>,
    pub post: ARichFormula<'bump>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RewriteKind<'bump> {
    Bool,
    Other(Function<'bump>),
}
