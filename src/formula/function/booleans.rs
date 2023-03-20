use crate::formula::sort::{
    builtins::{BOOL, CONDITION},
    sorted::{self, Sorted},
    RcSort, Sort,
};

use super::function_like::{HasArity, HasInputSorts, HasOutputSort, Named};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Booleans {
    And,
    Or,
    Not,
    Implies,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum CondBooleans {
    And,
    Or,
    Not,
    Implies,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Eval {
    Eval(Booleans),
    UnEval(CondBooleans),
}

static SORT_COND_2: [Sort<'static>; 2] = [CONDITION.as_sort(), CONDITION.as_sort()];
static SORT_COND_1: [Sort<'static>; 1] = [CONDITION.as_sort()];
static COND_REF: Sort<'static> = CONDITION.as_sort();

impl HasInputSorts for CondBooleans {
    type Ref = Sort<'static>;

    fn input_sorts<'sort>(&'sort self) -> &'sort [Self::Ref] {
        match self {
            CondBooleans::Not => SORT_COND_1.as_ref(),
            _ => SORT_COND_2.as_ref(),
        }
    }
}

impl HasOutputSort for CondBooleans {
    type Ref = Sort<'static>;

    fn output_sort<'sort>(&'sort self) -> &'sort Self::Ref {
        COND_REF.as_ref()
    }
}

static BOOL_REF: Sort<'static> = BOOL.as_sort();

impl HasOutputSort for Booleans {
    type Ref = Sort<'static>;

    fn output_sort<'sort>(&'sort self) -> &'sort Self::Ref {
        BOOL_REF.as_ref()
    }
}

impl HasOutputSort for Eval {
    type Ref = Sort<'static>;

    fn output_sort<'sort>(&'sort self) -> &'sort Self::Ref {
        match self {
            Eval::Eval(e) | Eval::UnEval(e) => e.output_sort(),
        }
    }
}

impl Named for Booleans {
    fn name(&self) -> &str {
        match self {
            Booleans::And => "and",
            Booleans::Or => "or",
            Booleans::Not => "not",
            Booleans::Implies => "=>",
        }
    }
}
impl Named for CondBooleans {
    fn name(&self) -> &str {
        match self {
            CondBooleans::And => "cand",
            CondBooleans::Or => "cor",
            CondBooleans::Not => "cnot",
            CondBooleans::Implies => "cimplies",
        }
    }
}

impl Named for Eval {
    fn name(&self) -> &str {
        match self {
            Eval::Eval(e) | Eval::UnEval(e) => e.name(),
        }
    }
}

impl<'a> Sorted<'a> for Booleans {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, sorted::SortedError> {
        match self {
            Booleans::Not if args.len() != 1 => Err(sorted::SortedError::WrongNumberOfArguments {
                expected: Some(1),
                got: Some(args.len()),
            }),
            Booleans::Implies if args.len() != 2 => {
                Err(sorted::SortedError::WrongNumberOfArguments {
                    expected: Some(2),
                    got: Some(args.len()),
                })
            }
            _ => Ok(self.output_sort()),
        }
    }
}

impl<'a> Sorted<'a> for CondBooleans {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, sorted::SortedError> {
        if args.len() != self.arity() {
            Err(sorted::SortedError::WrongNumberOfArguments {
                expected: Some(self.arity()),
                got: Some(args.len()),
            })
        } else {
            Ok(self.output_sort())
        }
    }
}

impl<'a> Sorted<'a> for Eval {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, sorted::SortedError> {
        match self {
            Eval::Eval(e) | Eval::UnEval(e) => e.sort(args),
        }
    }
}
