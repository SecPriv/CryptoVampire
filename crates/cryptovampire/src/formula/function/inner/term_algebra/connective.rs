use macro_attr::*;

use crate::formula::function::Function;
use crate::formula::function::builtin::*;
use crate::formula::function::signature::{FixedRefSignature, Impossible, Signature};
use crate::formula::function::traits::{Evaluatable, FixedSignature};
use crate::formula::sort::builtins::{CONDITION, MESSAGE};
use crate::formula::sort::sort_proxy::SortProxy;
use crate::{CustomDerive, static_signature};

macro_attr! {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy,
        CustomDerive!(evaluate, no_bump, 'bump),
        CustomDerive!(fixed_signature, no_bump, 'bump))]
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
    True,
    False,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Default)]
pub struct Equality();

impl Connective {
    pub fn name(&self) -> &'static str {
        match self {
            Connective::BaseConnective(x) => x.name(),
            Connective::Equality(_) => "ta$=",
        }
    }
}

static_signature!(EQ_SIGNATURE: (MESSAGE, MESSAGE) -> CONDITION);
impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Equality {
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        EQ_SIGNATURE.as_ref()
    }
}

pub const AND_NAME: &str = "ta$and";
pub const OR_NAME: &str = "ta$or";
pub const NOT_NAME: &str = "ta$not";
pub const IMPLIES_NAME: &str = "ta$implies";
pub const IFF_NAME: &str = "ta$iff";
pub const TRUE_NAME: &str = "ta$true";
pub const FALSE_NAME: &str = "ta$false";

impl BaseConnective {
    pub fn evaluated(&self) -> Function<'static> {
        match self {
            BaseConnective::And => *AND,
            BaseConnective::Or => *OR,
            BaseConnective::Not => *NOT,
            BaseConnective::Implies => *IMPLIES,
            BaseConnective::Iff => *EQUALITY,
            BaseConnective::True => *TRUE_F,
            BaseConnective::False => *FALSE_F,
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            BaseConnective::And => AND_NAME,
            BaseConnective::Or => OR_NAME,
            BaseConnective::Not => NOT_NAME,
            BaseConnective::Implies => IMPLIES_NAME,
            BaseConnective::Iff => IFF_NAME,
            BaseConnective::True => TRUE_NAME,
            BaseConnective::False => FALSE_NAME,
        }
    }
}

static_signature!(AND_SIGNATURE: (CONDITION, CONDITION) -> CONDITION);
static_signature!(OR_SIGNATURE: (CONDITION, CONDITION) -> CONDITION);
static_signature!(IMPLIES_SIGNATURE: (CONDITION, CONDITION) -> CONDITION);
static_signature!(IFF_SIGNATURE: (CONDITION, CONDITION) -> CONDITION);
static_signature!(NOT_SIGNATURE: (CONDITION) -> CONDITION);
static_signature!(TRUE_SIGNATURE: () -> CONDITION);
static_signature!(FALSE_SIGNATURE: () -> CONDITION);

impl<'bump> Evaluatable<'bump> for BaseConnective {
    fn get_evaluated(&self) -> Function<'bump> {
        self.evaluated()
    }
}

impl<'bump> Evaluatable<'bump> for Equality {
    fn get_evaluated(&self) -> Function<'bump> {
        *EQUALITY
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
            BaseConnective::True => TRUE_SIGNATURE.as_ref(),
            BaseConnective::False => FALSE_SIGNATURE.as_ref(),
        }
    }
}

// impl<'a, 'bump> MaybeFixedSignature<'a, 'bump> for Equality
// where
//     'bump: 'a,
// {
//     fn maybe_fixed_signature(&'a self) -> Option<FixedRefSignature<'a, 'bump>> {
//         None
//     }
// }
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
    type Args<'a>
        = [SortProxy<'bump>; 2]
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

    fn args_size(&self) -> std::ops::RangeInclusive<utils::infinity::Infinity<usize>> {
        2.into()..=2.into()
    }
}
