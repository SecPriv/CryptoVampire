use std::{
    ops::{Deref, RangeTo},
    usize,
};

use egg::{ENodeOrVar, Id, Language, RecExpr};

use crate::formula::grammar::Index;

#[derive(Debug)]
pub struct RefRecExpr<'a, L>(pub &'a [L]);

impl<'a, L> Clone for RefRecExpr<'a, L> {
    fn clone(&self) -> Self {
        Self(&self.0)
    }
}

impl<'a, L> Copy for RefRecExpr<'a, L> {}

impl<'a, L> RefRecExpr<'a, L> {
    pub fn get_checked(&self, id: Id) -> Option<Self> {
        let idx: usize = id.into();
        if idx < self.len() {
            Some(Self(&self.0[0..idx]))
        } else {
            None
        }
    }

    pub fn get(&self, id: Id) -> Self {
        self.get_checked(id).unwrap()
    }

    pub fn head(&self) -> Option<&'a L> {
        self.0.last()
    }
}
impl<'a, L: Language> RefRecExpr<'a, L> {
    pub fn ids<'b>(&'b self) -> impl Iterator<Item = Id> + use<'a, L> {
        self.0.iter().flat_map(|l| l.children()).copied()
    }

    pub fn children<'b>(&'b self) -> impl Iterator<Item = Self> {
      let tmp = *self;
      tmp.ids().map(move |id| tmp.get(id))
    }

    pub fn search(&self, f: impl FnMut(Self) -> bool) -> bool {
        self.children().any(f)
    }
}

impl<'a, L> RefRecExpr<'a, ENodeOrVar<L>> {
    pub fn can_collapse(&self) -> bool {
        self.iter().all(|l| matches!(l, ENodeOrVar::ENode(_)))
    }

    pub fn collapse(&self) -> Option<RecExpr<L>>
    where
        L: Clone,
    {
        let inner_vec: Option<Vec<_>> = self
            .iter()
            .map(|l| match l {
                ENodeOrVar::ENode(l) => Some(l.clone()),
                ENodeOrVar::Var(_) => None,
            })
            .collect();
        Some(inner_vec?.into())
    }
}

impl<'a, L> std::ops::Deref for RefRecExpr<'a, L> {
    type Target = [L];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a, L: Language> From<RefRecExpr<'a, L>> for egg::RecExpr<L> {
    fn from(value: RefRecExpr<'a, L>) -> Self {
        value.iter().cloned().collect()
    }
}

impl<'a, L> From<&'a RecExpr<L>> for RefRecExpr<'a, L> {
    fn from(value: &'a RecExpr<L>) -> Self {
        Self(&value)
    }
}

pub mod pattern {
    use egg::{ENodeOrVar, Language, PatternAst, RecExpr};

    use super::RefRecExpr;

    pub fn can_collapse<L: Language>(pattern: &PatternAst<L>) -> bool {
        RefRecExpr::from(pattern).can_collapse()
    }
}

pub trait AsRefRecExpr<L> {
    fn into_ref<'a>(&'a self) -> RefRecExpr<'a, L>;
}

impl<L> AsRefRecExpr<L> for RecExpr<L> {
    fn into_ref<'a>(&'a self) -> RefRecExpr<'a, L> {
        RefRecExpr(&self)
    }
}
