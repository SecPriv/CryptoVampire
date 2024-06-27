use crate::{
    formula::{
        function::{
            signature::FixedRefSignature,
            traits::{FixedSignature, MaybeEvaluatable},
        },
        sort::builtins::{CONDITION, MESSAGE, STEP},
    },
    static_signature,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum Macro {
    Condition,
    Message,
}

impl<'bump> MaybeEvaluatable<'bump> for Macro {
    fn maybe_get_evaluated(&self) -> Option<crate::formula::function::Function<'bump>> {
        None
    }
}

// for now
static_signature!(STEP_MESSAGE_SIGNATURE: (STEP) -> MESSAGE);
static_signature!(STEP_CONDITION_SIGNATURE: (STEP) -> CONDITION);

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Macro {
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        match self {
            Self::Condition => STEP_CONDITION_SIGNATURE.as_ref(),
            Self::Message => STEP_MESSAGE_SIGNATURE.as_ref(),
        }
    }
}

impl Macro {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Condition => "ta$cond",
            Self::Message => "ta$msg",
        }
    }
}
