use std::marker::PhantomData;

use crate::formula::container::Container;


#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum StepFunction<'bump> {
    Step(InnerStepFuction<'bump>),
    Pred
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerStepFuction<'bump> {
    tmp: PhantomData<&'bump ()>
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum StepPredicates {
    LessThan, Happens
}