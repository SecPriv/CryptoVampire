use std::sync::Arc;

use crate::formula::formula::ARichFormula;
use crate::formula::function::Function;
use crate::formula::sort::Sort;
use crate::formula::variable::Variable;

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

    pub fn comment(c: impl Into<Box<str>>) -> Self {
        Self::Comment(c.into())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rewrite<'bump> {
    pub kind: RewriteKind<'bump>,
    pub vars: Arc<[Variable<'bump>]>,
    pub pre: ARichFormula<'bump>,
    pub post: ARichFormula<'bump>,
}

pub type RewriteKind<'bump> = cryptovampire_smt::RewriteKind<Function<'bump>>;
