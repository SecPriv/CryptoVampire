use crate::{
    formula::{
        function::{
            builtin::{AND, EQUALITY, IFF, IMPLIES, NOT, OR},
            signature::FixedRefSignature,
            traits::{Evaluatable, FixedSignature, MaybeFixedSignature},
            Function,
        },
        sort::builtins::CONDITION,
    },
    static_signature, CustomDerive,
};

use macro_attr::*;

macro_attr! {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy,
        CustomDerive!(evaluate, no_bump, 'bump),
        CustomDerive!(maybe_fixed_signature, no_bump, 'bump))]
    pub enum Connective {
        BaseConnective(BaseConnective),
        Equality(Equality),
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum BaseConnective {
    And,
    Or,
    Not,
    Implies,
    Iff,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Equality();

impl BaseConnective {
    pub fn evaluated(&self) -> Function<'static> {
        match self {
            BaseConnective::And => AND.clone(),
            BaseConnective::Or => OR.clone(),
            BaseConnective::Not => NOT.clone(),
            BaseConnective::Implies => IMPLIES.clone(),
            BaseConnective::Iff => IFF.clone(),
        }
    }
}

static_signature!(AND_SIGNATURE: (CONDITION, CONDITION) -> CONDITION);
static_signature!(OR_SIGNATURE: (CONDITION, CONDITION) -> CONDITION);
static_signature!(IMPLIES_SIGNATURE: (CONDITION, CONDITION) -> CONDITION);
static_signature!(IFF_SIGNATURE: (CONDITION, CONDITION) -> CONDITION);
static_signature!(NOT_SIGNATURE: (CONDITION) -> CONDITION);

impl<'bump> Evaluatable<'bump> for BaseConnective {
    fn get_evaluated(&self) -> Function<'bump> {
        self.evaluated()
    }
}

impl<'bump> Evaluatable<'bump> for Equality {
    fn get_evaluated(&self) -> Function<'bump> {
        EQUALITY.clone()
    }
}

impl<'a, 'bump> FixedSignature<'a, 'bump> for BaseConnective
where
    'bump: 'a,
{
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        match self {
            BaseConnective::And => AND_SIGNATURE.as_ref(),
            BaseConnective::Or => OR_SIGNATURE.as_ref(),
            BaseConnective::Not => NOT_SIGNATURE.as_ref(),
            BaseConnective::Implies => IMPLIES_SIGNATURE.as_ref(),
            BaseConnective::Iff => IFF_SIGNATURE.as_ref(),
        }
    }
}

impl<'a, 'bump> MaybeFixedSignature<'a, 'bump> for Equality
where
    'bump: 'a,
{
    fn maybe_fixed_signature(&'a self) -> Option<FixedRefSignature<'a, 'bump>> {
        None
    }
}
// impl<'bump> Evaluatable<'bump> for Connective {
//     fn get_evaluated(&self) -> Function<'bump> {
//         match_as_trait!(self => {
//             Self::BaseConnective(x) | Self::Equality(x) => {x.get_evaluated()}
//         })
//     }
// }
