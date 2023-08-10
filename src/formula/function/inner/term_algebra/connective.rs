use crate::{
    formula::{
        function::{
            builtin::{AND, EQUALITY, IFF, IMPLIES, NOT, OR},
            signature::{FixedRefSignature, Impossible, Lazy, Signature},
            traits::{Evaluatable, FixedSignature, MaybeFixedSignature},
            Function,
        },
        sort::{builtins::CONDITION, sort_proxy::SortProxy},
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Default)]
pub struct Equality();

impl Connective {
    pub fn signature<'a, 'bump: 'a>(&'a self) -> impl Signature<'bump> + 'a {
        match self {
            Connective::BaseConnective(b) => Lazy::A(b.as_fixed_signature()),
            Connective::Equality(_) => Lazy::B(Equality::signature()),
        }
    }
}

impl Equality {
    pub fn signature<'bump>() -> EqualitySignature<'bump> {
        Default::default()
    }
}

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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Default)]
pub struct EqualitySignature<'bump> {
    left: SortProxy<'bump>,
    right: SortProxy<'bump>,
}

impl<'bump> Signature<'bump> for EqualitySignature<'bump> {
    type Args<'a> = [SortProxy<'bump>; 2]
    where
        Self: 'a,
        'bump: 'a;

    type FxSign = Impossible;

    fn out(&self) -> SortProxy<'bump> {
        CONDITION.as_sort().into()
    }

    fn args<'a>(&'a self) -> Self::Args<'a>
    where
        'bump: 'a,
    {
        [&self.left, &self.right].map(Clone::clone)
    }

    fn fast(self) -> Option<Self::FxSign> {
        None
    }

    fn args_size(&self) -> std::ops::RangeInclusive<crate::utils::infinity::Infinity<usize>> {
        2.into()..=2.into()
    }
}
