use static_init::dynamic;

use crate::formula::sort::{
    builtins::{StatSort, BOOL},
    sorted::{Sorted, SortedError},
    Sort,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Connective {
    And,
    Or,
    Not,
    Implies,
    Iff,
}

impl Connective {
    pub const fn name(&self) -> &'static str {
        match self {
            Connective::And => "and",
            Connective::Or => "or",
            Connective::Not => "not",
            Connective::Implies => "=>",
            Connective::Iff => "=",
        }
    }

    pub fn output_sort(&self) -> StatSort {
        BOOL.as_sort()
    }
}

#[dynamic]
static BOOL_2: [Sort<'static>; 2] = [BOOL.as_sort(), BOOL.as_sort()];
#[dynamic]
static BOOL_1: [Sort<'static>; 1] = [BOOL.as_sort()];

impl<'a> Sorted<'a> for Connective {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, SortedError> {
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct Equality();

impl Equality {
    pub const fn name(&self) -> &'static str {
        "="
    }

    pub fn output_sort(&self) -> StatSort {
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Booleans {
    Connective(Connective),
    Equality(Equality),
}

impl Booleans {
    pub const fn name(&self) -> &'static str {
        match self {
            Booleans::Connective(e) => e.name(),
            Booleans::Equality(e) => e.name(),
        }
    }

    pub fn output_sort(&self) -> StatSort {
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
