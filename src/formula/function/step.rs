use std::marker::PhantomData;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum StepFunction<'bump> {
    Step(InnerStepFuction<'bump>),
    Pred,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerStepFuction<'bump> {
    tmp: PhantomData<&'bump ()>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum StepPredicates {
    LessThan,
    Happens,
}

fn enlarge<'a, 'b>(q: StepFunction<'a>) -> StepFunction<'b>
where
    'a: 'b,
{
    q
}
