use macro_attr::*;
use utils::assert_variance;

use super::super::signature::FixedRefSignature;
use super::super::traits::{FixedSignature, MaybeEvaluatable};
use crate::formula::sort::builtins::STEP;
use crate::problem::step::Step;
use crate::{CustomDerive, static_signature};
macro_attr! {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone,
        CustomDerive!(maybe_evaluate, 'bump),
        CustomDerive!(fixed_signature, 'bump),
    )]
    pub enum StepFunction<'bump> {
        Step(InnerStepFuction<'bump>),
        Pred(Pred),
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerStepFuction<'bump> {
    step: Step<'bump>,
}

impl<'bump> From<Step<'bump>> for StepFunction<'bump> {
    fn from(value: Step<'bump>) -> Self {
        Self::Step(InnerStepFuction { step: value })
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Default)]
pub struct Pred();

impl<'bump> InnerStepFuction<'bump> {
    pub fn new(step: Step<'bump>) -> Self {
        Self { step }
    }

    pub fn step(&self) -> Step<'bump> {
        self.step
    }
}

impl<'bump> StepFunction<'bump> {
    pub fn name(&self) -> &str {
        match self {
            StepFunction::Pred(_) => "pred",
            StepFunction::Step(s) => s.step.name(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum StepPredicates {
    LessThan,
    Happens,
}

assert_variance!(StepFunction);

static_signature!(PRED_SIGNATURE: (STEP) -> STEP);

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Pred {
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        PRED_SIGNATURE.as_ref()
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for InnerStepFuction<'bump> {
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        FixedRefSignature {
            out: *STEP,
            args: self
                .step()
                .free_variables()
                .iter()
                .map(|v| v.sort)
                .collect(),
        }
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Pred {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}

impl<'bump> MaybeEvaluatable<'bump> for InnerStepFuction<'bump> {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}
