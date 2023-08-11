use crate::{
    formula::{
        function::traits::{FixedSignature, MaybeEvaluatable},
        sort::builtins::{MESSAGE, STEP},
    },
    static_signature,
};

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct Input;

impl Input {
    pub fn name(&self) -> &'static str {
        "input"
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Input {
    fn maybe_get_evaluated(&self) -> Option<crate::formula::function::Function<'bump>> {
        None
    }
}

static_signature!(INPUT_SIGNATURE: (STEP) -> MESSAGE);

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Input {
    fn as_fixed_signature(
        &'a self,
    ) -> crate::formula::function::signature::FixedRefSignature<'a, 'bump> {
        INPUT_SIGNATURE.as_ref()
    }
}
