use std::any::Any;
use std::fmt::Debug;
use std::sync::Arc;

use bon::Builder;
use egg::Analysis;
use golgge::{Rule, WeightedAnalysis};
use serde::Serialize;

use crate::{Lang, Problem};

pub struct RcRule(Arc<dyn for<'a> CVRuleTrait<'a>>);

pub(crate) trait CVRuleTrait<'a>:
    Any + Rule<Lang, PAnalysis<'a>, RcRule> + Sync + Send
{
}

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
pub trait PRule {
    /// Converts the rule into a `RcRule`
    fn into_mrc(self) -> RcRule;
}

impl<R> PRule for R
where
    R: for<'a> Rule<Lang, PAnalysis<'a>, RcRule>,
    R: Sized + Any + Sync + Send + 'static,
{
    /// Converts the rule into a reference-counted `RcRule`.
    fn into_mrc(self) -> RcRule {
        RcRule(Box::<dyn for<'a> CVRuleTrait<'a>>::from(Box::new(self)).into())
    }
}

impl<'a, R> CVRuleTrait<'a> for R where R: Any + Rule<Lang, PAnalysis<'a>, RcRule> + Sync + Send {}

impl<'a> Rule<Lang, PAnalysis<'a>, Self> for RcRule {
    fn search(
        &self,
        prgm: &mut golgge::Program<Lang, PAnalysis<'a>, Self>,
        goal: egg::Id,
    ) -> golgge::Dependancy {
        self.0.search(prgm, goal)
    }

    fn rebuild(&self, prgm: &golgge::Program<Lang, PAnalysis<'a>, Self>) {
        self.0.rebuild(prgm);
    }

    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        self.0.debug(f)
    }

    fn name(&self) -> std::borrow::Cow<'_, str> {
        self.0.name()
    }
}

impl Clone for RcRule {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl Debug for RcRule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.debug(f)
    }
}

impl<'a> AsRef<dyn CVRuleTrait<'a>> for RcRule {
    fn as_ref(&self) -> &dyn CVRuleTrait<'a> {
        self.0.as_ref()
    }
}
