use std::marker::PhantomData;

use bumpalo::Bump;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum StepFunction<'bump> {
    Step(InnerStepFuction<'bump>),
    Pred
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerStepFuction<'bump> {
    tmp: PhantomData<&'bump Bump>
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum StepPredicates {
    LessThan, Happens
}