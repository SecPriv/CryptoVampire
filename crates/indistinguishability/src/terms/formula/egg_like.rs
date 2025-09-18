use std::fmt::Display;
use std::rc::Rc;

use egg::{ENodeOrVar, Id, Language, RecExpr, Var};
use itertools::Itertools;
use logic_formula::{Destructed, Formula, Head, HeadSk};
use serde::Serialize;
use smallvec::SmallVec;

use crate::LangVar;
use crate::terms::formula::RecFOFormulaQuant;
use crate::terms::{FOBinder, Function, Sort, CONS, NIL};

const SIZE: usize = 3;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Serialize)]
pub struct InnerLang {
    pub head: Function,
    pub args: SmallVec<[Id; SIZE]>,
}

impl InnerLang {
    pub const fn new_const(head: Function, args: [Id; SIZE], len: usize) -> Self {
        assert!(len <= SIZE);

        Self {
            head,
            args: unsafe {
                // we checked the length just above
                SmallVec::from_const_with_len_unchecked(args, len)
            },
        }
    }

    pub fn new<I: IntoIterator<Item = Id>>(head: Function, args: I) -> Self {
        Self {
            head,
            args: args.into_iter().collect(),
        }
    }

}

impl Language for InnerLang {
    type Discriminant = Function;

    fn discriminant(&self) -> Self::Discriminant {
        self.head.clone()
    }

    fn matches(&self, other: &Self) -> bool {
        self.head == other.head && self.args.len() == other.args.len()
    }

    fn children(&self) -> &[Id] {
        &self.args
    }

    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.args
    }
}

impl Display for InnerLang {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.head)
    }
}