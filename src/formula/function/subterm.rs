use std::rc::Rc;

use crate::{environement::environement::Environement, problem::crypto_assumptions::SubtermNonce};

use super::InnerFunction;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Subterm<'bump> {
    pub subterm: Subsubterm<'bump>,
    pub kind: SubtermKind,
    pub name: String,
}

impl<'bump> Subterm<'bump> {
    pub fn into_inner_function(self) -> InnerFunction<'bump> {
        InnerFunction::Subterm(self)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum SubtermKind {
    Regular,
    Vampire,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Subsubterm<'bump> {
    Nonce(Rc<SubtermNonce<'bump>>),
}

fn enlarge<'a, 'b>(q: Subterm<'a>) -> Subterm<'b>
where
    'a: 'b,
{
    q
}

impl<'bump> From<Environement<'bump>> for SubtermKind {
    fn from(env: Environement<'bump>) -> Self {
        if env.use_vampire_subterm() {
            Self::Vampire
        } else {
            Self::default()
        }
    }
}

impl Default for SubtermKind {
    fn default() -> Self {
        Self::Regular
    }
}
