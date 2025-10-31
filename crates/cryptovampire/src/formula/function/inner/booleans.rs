use super::super::traits::{MaybeEvaluatable, MaybeFixedSignature};
use crate::formula::function::signature::{Lazy, Signature};
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::BOOL;
use crate::formula::sort::sorted::{Sorted, SortedError};
use crate::{CustomDerive, static_signature};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Connective {
    And,
    Or,
    Not,
    Implies,
    // Iff,
    True,
    False,
}

impl Connective {
    pub const fn name(&self) -> &'static str {
        match self {
            Connective::And => "and",
            Connective::Or => "or",
            Connective::Not => "not",
            Connective::Implies => "=>",
            // Connective::Iff => "=",
            Connective::True => "true",
            Connective::False => "false",
        }
    }

    pub fn output_sort<'a>(&self) -> Sort<'a> {
        BOOL.as_sort()
    }

    pub fn signature<'a, 'bump: 'a>(&'a self) -> impl Signature<'bump> + 'a {
        match self {
            Connective::And => Lazy::A(signatures::InfiniteBoolSignature),
            Connective::Or => Lazy::A(signatures::InfiniteBoolSignature),
            Connective::Not => Lazy::B(NOT_SIGNATURE.as_ref()),
            Connective::Implies => Lazy::B(IMPLIES_SIGNATURE.as_ref()),
            // Connective::Iff => Lazy::B(IFF_SIGNATURE.as_ref()),
            Connective::True => Lazy::B(TRUE_SIGNATURE.as_ref()),
            Connective::False => Lazy::B(FALSE_SIGNATURE.as_ref()),
        }
    }
}

// #[dynamic]
// static BOOL_2: [Sort<'static>; 2] = [BOOL.as_sort(), BOOL.as_sort()];
// #[dynamic]
// static BOOL_1: [Sort<'static>; 1] = [BOOL.as_sort()];

impl<'a> Sorted<'a> for Connective {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, SortedError> {
        match &self {
            Connective::True | Connective::False => Ok(BOOL.as_sort()),
            _ => {
                if args.iter().any(|s| s != &BOOL.as_sort()) {
                    Err(SortedError::WrongArguments {
                        expected: format!("only {:?}", BOOL.as_sort()),
                        got: format!("{:?}", args),
                    })
                } else {
                    match self {
                        Connective::Not => Err(SortedError::WrongArguments {
                            expected: format!("1 arguments of type {:?}", BOOL.as_sort()),
                            got: format!("{:?}", args),
                        }),
                        Connective::Implies /* | Connective::Iff */ if args.len() != 2 => {
                            Err(SortedError::WrongArguments {
                                expected: format!("2 arguments of type {:?}", BOOL.as_sort()),
                                got: format!("{:?}", args),
                            })
                        }
                        _ => Ok(BOOL.as_sort()),
                    }
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct Equality();

impl Equality {
    pub const fn name(&self) -> &'static str {
        "="
    }

    pub fn output_sort<'a>(&self) -> Sort<'a> {
        BOOL.as_sort()
    }

    pub fn signature<'a>() -> impl Signature<'a> {
        signatures::EqualitySignature::default()
    }
}

impl<'a> Sorted<'a> for Equality {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, SortedError> {
        if args.len() != 2 || args.first() != args.get(1) {
            Err(SortedError::WrongArguments {
                expected: "2 arguments the same type".to_string(),
                got: format!("{:?}", args),
            })
        } else {
            Ok(BOOL.as_sort())
        }
    }
}

use macro_attr::*;

macro_attr! {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy,
        CustomDerive!(maybe_evaluate, no_bump, 'bump),
        CustomDerive!(maybe_fixed_signature, no_bump, 'bump))]
    pub enum Booleans {
        Connective(Connective),
        Equality(Equality),
    }
}

impl Booleans {
    pub const fn name(&self) -> &'static str {
        match self {
            Booleans::Connective(e) => e.name(),
            Booleans::Equality(e) => e.name(),
        }
    }

    pub fn output_sort<'a>(&self) -> Sort<'a> {
        BOOL.as_sort()
    }

    pub fn signature<'a, 'bump: 'a>(&'a self) -> impl Signature<'bump> + 'a {
        match self {
            Booleans::Connective(x) => Lazy::A(x.signature()),
            Booleans::Equality(_) => Lazy::B(Equality::signature()),
        }
    }
}

impl<'a> Sorted<'a> for Booleans {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, SortedError> {
        match self {
            Booleans::Connective(e) => e.sort(args),
            Booleans::Equality(e) => e.sort(args),
        }
    }
}

static_signature!(IMPLIES_SIGNATURE: (BOOL, BOOL) -> BOOL);
static_signature!(IFF_SIGNATURE: (BOOL, BOOL) -> BOOL);
static_signature!(NOT_SIGNATURE: (BOOL) -> BOOL);
static_signature!(TRUE_SIGNATURE: () -> BOOL);
static_signature!(FALSE_SIGNATURE: () -> BOOL);

impl<'a, 'bump: 'a> MaybeFixedSignature<'a, 'bump> for Connective {
    fn maybe_fixed_signature(
        &'a self,
    ) -> Option<super::super::signature::FixedRefSignature<'a, 'bump>> {
        match self {
            Connective::Not => Some(NOT_SIGNATURE.as_ref()),
            Connective::Implies => Some(IMPLIES_SIGNATURE.as_ref()),
            // Connective::Iff => Some(IFF_SIGNATURE.as_ref()),
            Connective::True => Some(TRUE_SIGNATURE.as_ref()),
            Connective::False => Some(FALSE_SIGNATURE.as_ref()),
            _ => None,
        }
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Connective {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}

impl<'a, 'bump: 'a> MaybeFixedSignature<'a, 'bump> for Equality {
    fn maybe_fixed_signature(
        &'a self,
    ) -> Option<super::super::signature::FixedRefSignature<'a, 'bump>> {
        None
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Equality {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}

mod signatures {
    use std::iter::Repeat;

    use utils::infinity::Infinity;

    use crate::formula::function::signature::{Impossible, Signature};
    use crate::formula::sort::builtins::BOOL;
    use crate::formula::sort::sort_proxy::SortProxy;
    use crate::static_signature;

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
            BOOL.as_sort().into()
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

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Default, Copy)]
    pub struct InfiniteBoolSignature;

    static_signature!(BINARY_SIGNATURE: (BOOL, BOOL) -> BOOL);
    impl<'bump> Signature<'bump> for InfiniteBoolSignature {
        type Args<'a>
            = Repeat<SortProxy<'bump>>
        where
            Self: 'a,
            'bump: 'a;

        type FxSign = Impossible; // FixedRefSignature<'static, 'static>;

        fn out(&self) -> SortProxy<'bump> {
            BOOL.as_sort().into()
        }

        fn args<'a>(&'a self) -> Self::Args<'a>
        where
            'bump: 'a,
        {
            std::iter::repeat(BOOL.as_sort().into())
        }

        fn fast(self) -> Option<Self::FxSign> {
            // Some(BINARY_SIGNATURE.as_ref())
            None
        }

        fn args_size(&self) -> std::ops::RangeInclusive<Infinity<usize>> {
            0.into()..=Infinity::HighInfinty
        }
    }
}
