use std::sync::atomic::{self, AtomicUsize};

use crate::formula::{formula::RichFormula, variable::Variable};

static N_QUANTIFIERS: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum InnerQuantifier<'bump> {
    Forall {
        content: Box<RichFormula<'bump>>, // Rich formula
    },
    Exists {
        content: Box<RichFormula<'bump>>, // Rich formula
    },
    FindSuchThat {
        condition: Box<RichFormula<'bump>>, // Rich formula
        success: Box<RichFormula<'bump>>,   // Rich formula
        faillure: Box<RichFormula<'bump>>,  // Rich formula
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Quantifier<'bump> {
    pub bound_variables: Box<[Variable<'bump>]>,
    pub free_variables: Box<[Variable<'bump>]>,
    id: usize,
    inner: InnerQuantifier<'bump>,
}

pub fn get_next_quantifer_id() -> usize {
    // let id = N_QUANTIFIERS.load(atomic::Ordering::Acquire);
    let id = N_QUANTIFIERS.fetch_add(1, atomic::Ordering::AcqRel);
    if id == usize::MAX {
        panic!(
            "what do you think you're doing ??? {} quantifiers should be enough !\nI can't ensure that the soundness of future quantifier, so I stop here.",
            usize::MAX - 1
        )
    }
    id
}

impl<'bump> Quantifier<'bump> {
    pub fn get_content(&self) -> std::boxed::Box<[&RichFormula<'bump>]> {
        match &self.inner {
            InnerQuantifier::Forall { content } | InnerQuantifier::Exists { content } => {
                std::boxed::Box::new([content.as_ref()])
            }
            InnerQuantifier::FindSuchThat {
                condition,
                success,
                faillure,
            } => std::boxed::Box::new([condition.as_ref(), success.as_ref(), faillure.as_ref()]),
        }
    }
}
