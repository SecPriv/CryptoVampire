use std::sync::atomic::{self, AtomicUsize};

use crate::formula::{
    formula::RichFormula,
    function::{
        signature::FixedRefSignature,
        traits::{FixedSignature, MaybeEvaluatable},
    },
    sort::builtins::{CONDITION, MESSAGE},
    variable::Variable,
};

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
    pub id: usize,
    pub inner: InnerQuantifier<'bump>,
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

    pub fn inner(&self) -> &InnerQuantifier<'bump> {
        &self.inner
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Quantifier<'bump> {
    fn maybe_get_evaluated(&self) -> Option<crate::formula::function::Function<'bump>> {
        None
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Quantifier<'bump> {
    fn as_fixed_signature(
        &'a self,
    ) -> crate::formula::function::signature::FixedRefSignature<'a, 'bump> {
        let out = match self.inner {
            InnerQuantifier::FindSuchThat { .. } => MESSAGE.clone(),
            InnerQuantifier::Exists { .. } | InnerQuantifier::Forall { .. } => CONDITION.clone(),
        };

        FixedRefSignature {
            out,
            args: self.bound_variables.iter().map(|v| v.sort).collect(),
        }
    }
}
