use std::sync::atomic::AtomicUsize;

use bumpalo::boxed::Box;

use crate::formula::formula::Variable;

static N_QUANTIFIERS: AtomicUsize = 0;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum InnerQuantifier<'bump> {
    Forall{
        content: Box<'bump, ()> // Rich formula
    },
    Exists{
        content: Box<'bump, ()> // Rich formula
    },
    FindSuchThat {
        condition : Box<'bump, ()>, // Rich formula
        success : Box<'bump, ()>, // Rich formula
        faillure : Box<'bump, ()> // Rich formula
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Quantifier<'bump> {
    pub bound_variables: Box<'bump, [Variable<'bump>]>,
    pub free_variables: Box<'bump, [Variable<'bump>]>,
    id: usize,
    inner: InnerQuantifier<'bump>
}

pub fn get_next_quantifer_id() -> usize {
    let id = N_QUANTIFIERS;
    N_QUANTIFIERS.checked_add(1).unwrap();
    id
}