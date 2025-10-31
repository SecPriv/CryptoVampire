use std::fmt::Display;
use std::sync::Arc;
use std::sync::atomic::{self, AtomicUsize};

use itertools::{Either, Itertools};
use utils::string_ref::StrRef;

use crate::formula::formula::ARichFormula;
use crate::formula::function::signature::FixedRefSignature;
use crate::formula::function::traits::{FixedSignature, MaybeEvaluatable};
use crate::formula::sort::builtins::{CONDITION, MESSAGE};
use crate::formula::variable::Variable;

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

    pub fn name(&self) -> &'static str {
        match self {
            InnerQuantifier::Forall { .. } => "ta$forall",
            InnerQuantifier::Exists { .. } => "ta$exists",
            InnerQuantifier::FindSuchThat { .. } => "ta$find_such_that",
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Quantifier<'bump> {
    pub bound_variables: Arc<[Variable<'bump>]>,
    pub free_variables: Arc<[Variable<'bump>]>,
    pub id: usize,
    pub inner: InnerQuantifier<'bump>,
}

impl<'bump> Display for Quantifier<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.inner {
            InnerQuantifier::Forall { .. } => write!(f, "forall"),
            InnerQuantifier::Exists { .. } => write!(f, "exists"),
            InnerQuantifier::FindSuchThat { .. } => write!(f, "findst"),
        }?;
        write!(f, "#{}", self.id)?;
        write!(f, "{{{}}}", self.free_variables.iter().join(", "))?;
        write!(f, " ({})", self.bound_variables.iter().join(", "))?;
        write!(f, " {{ {} }}", self.get_content().iter().join(" }{ "))
    }
}

pub fn get_next_quantifer_id() -> usize {
    // let id = N_QUANTIFIERS.load(atomic::Ordering::Acquire);
    let id = N_QUANTIFIERS.fetch_add(1, atomic::Ordering::AcqRel);
    if id == usize::MAX {
        panic!(
            "what do you think you're doing??? {} quantifiers should be enough!\nI can't ensure \
             that the soundness of future quantifier, so I stop here.",
            usize::MAX - 1
        )
    }
    id
}

impl<'bump> Quantifier<'bump> {
    pub fn get_content(&self) -> Box<[ARichFormula<'bump>]> {
        self.get_content_iter().cloned().collect()
    }

    pub fn get_content_iter<'a>(
        &'a self,
    ) -> impl ExactSizeIterator<Item = &'a ARichFormula<'bump>> {
        match &self.inner {
            InnerQuantifier::Forall { content } | InnerQuantifier::Exists { content } => {
                Either::Left([content])
            }
            InnerQuantifier::FindSuchThat {
                condition,
                success,
                faillure,
            } => Either::Right([condition, success, faillure]),
        }
        .into_iter()
    }

    pub fn inner(&self) -> &InnerQuantifier<'bump> {
        &self.inner
    }

    pub fn name<'a>(&self) -> StrRef<'a> {
        format!("{}${}", self.inner.name(), self.id).into()
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
            InnerQuantifier::FindSuchThat { .. } => *MESSAGE,
            InnerQuantifier::Exists { .. } | InnerQuantifier::Forall { .. } => *CONDITION,
        };

        FixedRefSignature {
            out,
            args: self.free_variables.iter().map(|v| v.sort).collect(),
        }
    }
}
