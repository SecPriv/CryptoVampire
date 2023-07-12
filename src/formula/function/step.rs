use std::marker::PhantomData;

use crate::{assert_variance, problem::step::Step};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum StepFunction<'bump> {
    Step(InnerStepFuction<'bump>),
    Pred,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerStepFuction<'bump> {
    step: Step<'bump>,
}

impl<'bump> InnerStepFuction<'bump> {
    pub fn new(step: Step<'bump>) -> Self {
        Self { step }
    }

    pub fn step(&self) -> Step {
        self.step
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum StepPredicates {
    LessThan,
    Happens,
}

assert_variance!(StepFunction);
