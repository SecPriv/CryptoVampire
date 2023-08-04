use crate::{
    formula::sort::{
        builtins::BOOL,
        sorted::{Sorted, SortedError},
        Sort,
    },
    static_signature, CustomDerive,
};

use super::super::traits::{MaybeEvaluatable, MaybeFixedSignature};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Connective {
    And,
    Or,
    Not,
    Implies,
    Iff,
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
            Connective::Iff => "=",
            Connective::True => "true",
            Connective::False => "false",
        }
    }

    pub fn output_sort<'a>(&self) -> Sort<'a> {
        BOOL.as_sort()
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
                        Connective::Implies | Connective::Iff if args.len() != 2 => {
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
}

impl<'a> Sorted<'a> for Equality {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, SortedError> {
        if args.len() != 2 || args.get(0) != args.get(1) {
            Err(SortedError::WrongArguments {
                expected: format!("2 arguments the same type"),
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
            Connective::Iff => Some(IFF_SIGNATURE.as_ref()),
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
