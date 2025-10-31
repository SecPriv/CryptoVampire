use crate::formula::function::traits::{FixedSignature, MaybeEvaluatable};
use crate::formula::sort::builtins::{CONDITION, MESSAGE};
use crate::static_signature;

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct IfThenElse;

impl IfThenElse {
    pub fn name(&self) -> &'static str {
        "ta$ite"
    }
}

impl<'bump> MaybeEvaluatable<'bump> for IfThenElse {
    fn maybe_get_evaluated(&self) -> Option<crate::formula::function::Function<'bump>> {
        None
    }
}

// for now
static_signature!(ITE_SIGNATURE: (CONDITION, MESSAGE, MESSAGE) -> MESSAGE);

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for IfThenElse {
    fn as_fixed_signature(
        &'a self,
    ) -> crate::formula::function::signature::FixedRefSignature<'a, 'bump> {
        ITE_SIGNATURE.as_ref()
    }
}
