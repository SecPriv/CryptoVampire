use std::fmt::Display;
use std::rc::Rc;

use egg::{Analysis, Id, Language};

use crate::{Program, Rule};

/// Represents a single item in a proof, detailing the rule applied and the e-class IDs involved.
#[derive(Clone)]
pub struct ProofItem<L: Language, N: Analysis<L>> {
    /// The rule that was applied.
    pub rule: Rc<dyn Rule<L, N>>,
    /// The e-class IDs involved in the proof step.
    pub ids: Vec<Id>,
    /// An optional side condition for the proof step.
    pub side_condition: Option<Rc<dyn Display>>,
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
pub struct Proof<'a, L: Language, N: Analysis<L>> {
    /// A reference to the program that generated the proof.
    prog: &'a Program<L, N>,
    /// The ID of the e-class for which the proof was generated.
    id: Id,
}
