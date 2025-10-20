use std::fmt::Display;

use egg::{ENodeOrVar, Id, Language};
use log::trace;
use logic_formula::Formula;
use serde::Serialize;
use smallvec::SmallVec;
use utils::implvec;

use crate::terms::{Function, Variable};

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
        // trace!("in 'maches': {self} <-> {other}");
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

trait Sealed {}

pub trait EggLanguage: Sealed + Sealed {
    fn mk_fun_application(head: Function, args: implvec!(Id)) -> Self;
    fn mk_variable(var: &Variable) -> Self;
}

impl Sealed for crate::Lang {}
impl Sealed for crate::LangVar {}

impl EggLanguage for crate::Lang {
    fn mk_fun_application(head: Function, args: implvec!(Id)) -> Self {
        head.app_id(args)
    }

    fn mk_variable(var: &Variable) -> Self {
        unimplemented!()
    }
}

// $crate::terms::formula::egg::EggLanguage
impl EggLanguage for crate::LangVar {
    fn mk_fun_application(head: Function, args: implvec!(Id)) -> Self {
        ENodeOrVar::ENode(head.app_id(args))
    }

    fn mk_variable(var: &Variable) -> Self {
        var.as_lang_var()
    }
}
