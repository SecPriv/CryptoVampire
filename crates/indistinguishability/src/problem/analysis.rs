use std::rc::Rc;

use bon::Builder;
use egg::Analysis;
use golgge::{Rule, WeightedAnalysis};
use serde::Serialize;

use crate::{Lang, Problem};

/// A reference counted rule
pub type RcRule = Rc<dyn for<'a> Rule<Lang, PAnalysis<'a>>>;

/// The analysis for the problem
#[derive(Debug, Serialize, Builder)]
pub struct PAnalysis<'a> {
    /// A mutable reference to the problem instance.
    #[serde(skip)]
    pbl: &'a mut Problem,
}

impl<'a> PAnalysis<'a> {
    /// Returns a mutable reference to the problem
    pub fn pbl_mut(&mut self) -> &mut &'a mut Problem {
        &mut self.pbl
    }

    /// Returns a reference to the problem
    pub fn pbl(&self) -> &&'a mut Problem {
        &self.pbl
    }
}

impl<'a> Analysis<Lang> for PAnalysis<'a> {
    /// The data associated with each e-class. `PAnalysis` does not store per-node data.
    type Data = ();

    /// Creates a new analysis data for an e-node.
    ///
    /// This implementation does nothing as `PAnalysis` does not store per-node data.
    fn make(_egraph: &mut egg::EGraph<Lang, Self>, _enode: &Lang) -> Self::Data {}

    /// Merges two analysis data. Since `PAnalysis` does not store per-node data,
    /// this method always returns `DidMerge(false, false)`.
    fn merge(&mut self, _a: &mut Self::Data, _b: Self::Data) -> egg::DidMerge {
        egg::DidMerge(false, false)
    }
}

impl<'a> WeightedAnalysis<Lang> for PAnalysis<'a> {
    type Weight = ();

    /// Returns the weight for the given analysis data.
    ///
    /// This implementation returns `()` as `PAnalysis` does not use weights.
    fn get_weight(_data: &Self::Data) -> Self::Weight {}
}

/// A trait for rules that can be converted into a `RcRule`
pub trait PRule: for<'a> Rule<Lang, PAnalysis<'a>> {
    /// Converts the rule into a `RcRule`
    fn into_mrc(self) -> RcRule;
}

impl<R> PRule for R
where
    R: for<'a> Rule<Lang, PAnalysis<'a>>,
    R: Sized + 'static,
{
    /// Converts the rule into a reference-counted `RcRule`.
    fn into_mrc(self) -> RcRule {
        Box::<dyn for<'a> Rule<Lang, PAnalysis<'a>>>::from(Box::new(self)).into()
    }
}
