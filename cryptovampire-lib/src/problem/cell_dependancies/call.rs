//! A bunch a struct to descibe all the way to call a cell or an input

use std::sync::Arc;

use crate::{
    formula::formula::ARichFormula,
    problem::{cell::MemoryCell, step::Step},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum OutGoingCall<'bump> {
    Input(InputCall<'bump>),
    Cell(CellCall<'bump>),
}

/// call `cell(args, step)`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CellCall<'bump> {
    pub cell: MemoryCell<'bump>,
    pub timepoint: StepCall<'bump>,
    pub args: Arc<[ARichFormula<'bump>]>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InputCall<'bump> {
    pub step: StepCall<'bump>,
    // pub args: &'pbl [RichFormula],
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum StepCall<'bump> {
    Step(Step<'bump>),
    General(ARichFormula<'bump>),
}
