use std::rc::Rc;

use bon::Builder;
use egg::Analysis;
use golgge::{Rule, WeightedAnalysis};
use serde::Serialize;

use crate::{Lang, Problem};

pub type RcRule = Rc<dyn for<'a> Rule<Lang, PAnalysis<'a>>>;

#[derive(Debug, Serialize, Builder)]
pub struct PAnalysis<'a> {
    #[serde(skip)]
    pbl: &'a mut Problem,
}

impl<'a> PAnalysis<'a> {
    pub fn pbl_mut(&mut self) -> &mut &'a mut Problem {
        &mut self.pbl
    }

    pub fn pbl(&self) -> &&'a mut Problem {
        &self.pbl
    }
}

impl<'a> Analysis<Lang> for PAnalysis<'a> {
    type Data = ();

    fn make(egraph: &mut egg::EGraph<Lang, Self>, enode: &Lang) -> Self::Data {}

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        egg::DidMerge(false, false)
    }
}

impl<'a> WeightedAnalysis<Lang> for PAnalysis<'a> {
    type Weight = ();

    fn get_weight(data: &Self::Data) -> Self::Weight {}
}

pub trait PRule: for<'a> Rule<Lang, PAnalysis<'a>> {
    fn into_mrc(self) -> RcRule;
}

impl<R> PRule for R
where
    R: for<'a> Rule<Lang, PAnalysis<'a>>,
    R: Sized + 'static,
{
    fn into_mrc(self) -> RcRule {
        Box::<dyn for<'a> Rule<Lang, PAnalysis<'a>>>::from(Box::new(self)).into()
    }
}
