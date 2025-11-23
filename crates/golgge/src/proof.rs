use std::any::Any;
use std::fmt::Display;
use std::rc::Rc;
#[cfg(feature = "sync")]
use std::sync::Arc;

use egg::{Analysis, Id, Language};

use crate::program::{Rebuildable, Status};
use crate::{Program, Rule, canonicalize_id};

#[cfg(feature = "sync")]
pub type Payload = Arc<dyn Any + Sync + Send>;
#[cfg(not(feature = "sync"))]
pub type Payload = Rc<dyn Any>;

/// Represents a single item in a proof, detailing the rule applied and the e-class IDs involved.
pub struct ProofItem<R> {
    /// The rule that was applied.
    pub rule: R,
    /// The e-class IDs involved in the proof step.
    pub ids: Vec<Id>,
    /// An optional side condition for the proof step.
    pub payload: Option<Payload>,
}

impl<R: Clone> Clone for ProofItem<R> {
    fn clone(&self) -> Self {
        Self {
            rule: self.rule.clone(),
            ids: self.ids.clone(),
            payload: self.payload.clone(),
        }
    }
}

/// Represents the result of a search operation.
#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SearchResult {
    /// The search failed.
    #[default]
    False,
    /// The search succeeded, returning the ID of the proven e-class.
    True(Id),
}

impl SearchResult {
    /// Returns `true` if the search result is `True`.
    pub fn as_bool(&self) -> bool {
        matches!(self, Self::True(_))
    }
}

/// Represents a proof for a given e-class.
#[allow(dead_code)]
pub struct Proof<'a, L: Language, N: Analysis<L>, R> {
    /// A reference to the program that generated the proof.
    prog: &'a Program<L, N, R>,
    /// The ID of the e-class for which the proof was generated.
    id: Id,
}

impl<L: Language, N: Analysis<L>, R> Rebuildable<L, N> for ProofItem<R> {
    fn rebuild(&mut self, egraph: &egg::EGraph<L, N>) {
        for id in &mut self.ids {
            *id = canonicalize_id(*id, egraph)
        }
    }
}

impl<R> From<Option<ProofItem<R>>> for Status<R> {
    fn from(value: Option<ProofItem<R>>) -> Self {
        match value {
            Some(proof) => Self::True(proof),
            None => Self::False,
        }
    }
}
