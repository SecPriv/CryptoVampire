use std::fmt::Display;

use egg::{Analysis, EGraph, Id};
use utils::match_eq;

use crate::Lang;
use crate::terms::{Function, LEFT, RIGHT};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Side {
    Left,
    Right,
}

impl From<Side> for Function {
    fn from(value: Side) -> Self {
        match value {
            Side::Left => LEFT.const_clone(),
            Side::Right => RIGHT.const_clone(),
        }
    }
}

impl Display for Side {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Left => write!(f, "left"),
            Self::Right => write!(f, "right"),
        }
    }
}

impl Side {
    pub fn try_from_fn(f: &Function) -> Option<Self> {
        match_eq!(f => {
          LEFT => {Some(Self::Left)},
          RIGHT => {Some(Self::Right)},
          _ => {None}
        })
    }

    pub fn try_from_egraph<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> Option<Self> {
        egraph[id]
            .nodes
            .iter()
            .find_map(|Lang { head, .. }| Self::try_from_fn(head))
    }

    pub fn get_id<N: Analysis<Lang>>(self, egraph: &mut EGraph<Lang, N>) -> Id {
        egraph.add(Function::from(self).app_id([]))
    }
}
