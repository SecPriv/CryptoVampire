use std::rc::Rc;

use crate::{
    environement::environement::Environement,
    problem::crypto_assumptions::{SubtermEufCmaMacKey, SubtermEufCmaMacMain, SubtermNonce},
};

use super::InnerFunction;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Subterm<'bump> {
    pub subterm: Subsubterm<'bump>,
    pub name: String,
}

impl<'bump> Subterm<'bump> {
    pub fn into_inner_function(self) -> InnerFunction<'bump> {
        InnerFunction::Subterm(self)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Subsubterm<'bump> {
    Nonce(Rc<SubtermNonce<'bump>>),
    EufCmaMacMain(Rc<SubtermEufCmaMacMain<'bump>>),
    EufCmaMacKey(Rc<SubtermEufCmaMacKey<'bump>>),
}

fn _enlarge<'a, 'b>(q: Subterm<'a>) -> Subterm<'b>
where
    'a: 'b,
{
    q
}
