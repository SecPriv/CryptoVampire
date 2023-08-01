use crate::formula::function::traits::{MaybeEvaluatable, MaybeFixedSignature};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct IfThenElse;

impl<'a, 'bump: 'a> MaybeFixedSignature<'a, 'bump> for IfThenElse {
    fn maybe_fixed_signature(
        &'a self,
    ) -> Option<super::super::signature::FixedRefSignature<'a, 'bump>> {
        None
    }
}

impl<'bump> MaybeEvaluatable<'bump> for IfThenElse {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}
