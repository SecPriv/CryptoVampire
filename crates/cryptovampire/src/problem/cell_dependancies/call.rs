//! A bunch a struct to descibe all the way to call a cell or an input

use crate::formula::formula::ARichFormula;
use crate::problem::step::Step;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InputCall<'bump> {
    pub step: StepCall<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum StepCall<'bump> {
    Step(Step<'bump>),
    General(ARichFormula<'bump>),
}
