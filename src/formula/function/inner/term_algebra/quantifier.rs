use std::sync::{
    atomic::{self, AtomicUsize},
    Arc,
};

use crate::formula::{
    formula::ARichFormula,
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
        content: ARichFormula<'bump>, // Rich formula
    },
    Exists {
        content: ARichFormula<'bump>, // Rich formula
    },
    FindSuchThat {
        condition: ARichFormula<'bump>, // Rich formula
        success: ARichFormula<'bump>,   // Rich formula
        faillure: ARichFormula<'bump>,  // Rich formula
    },
}

impl<'bump> InnerQuantifier<'bump> {
    /// Returns `true` if the inner quantifier is [`FindSuchThat`].
    ///
    /// [`FindSuchThat`]: InnerQuantifier::FindSuchThat
    #[must_use]
    pub fn is_find_such_that(&self) -> bool {
        matches!(self, Self::FindSuchThat { .. })
    }

    /// Returns `true` if the inner quantifier is [`Exists`].
    ///
    /// [`Exists`]: InnerQuantifier::Exists
    #[must_use]
    pub fn is_exists(&self) -> bool {
        matches!(self, Self::Exists { .. })
    }

    /// Returns `true` if the inner quantifier is [`Forall`].
    ///
    /// [`Forall`]: InnerQuantifier::Forall
    #[must_use]
    pub fn is_forall(&self) -> bool {
        matches!(self, Self::Forall { .. })
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Quantifier<'bump> {
    pub bound_variables: Arc<[Variable<'bump>]>,
    pub free_variables: Arc<[Variable<'bump>]>,
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
    pub fn get_content(&self) -> Box<[ARichFormula<'bump>]> {
        match &self.inner {
            InnerQuantifier::Forall { content } | InnerQuantifier::Exists { content } => {
                Box::new([content.shallow_copy()])
            }
            InnerQuantifier::FindSuchThat {
                condition,
                success,
                faillure,
            } => Box::new([condition, success, faillure].map(|fa| fa.shallow_copy())),
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
