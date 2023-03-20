use crate::formula::sort::{Sort, builtins::{CONDITION, BOOL}, RcSort};

use super::function_like::{HasOutputSort, HasInputSorts};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Equalities {
    Eq, Neq
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum CondEqualities {
    Eq(RcSort), Neq(RcSort)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone,  Hash)]
pub enum Eval {
    Eval(Equalities),
    UnEval(CondEqualities),
}

static COND_REF: Sort<'static> = CONDITION.as_sort();
static BOOL_REF: Sort<'static> = BOOL.as_sort();

impl HasOutputSort for Equalities {
    type Ref = Sort<'static>;

    fn output_sort<'sort>(&'sort self) -> &'sort Self::Ref {
        BOOL_REF.as_ref()
    }
}

impl HasOutputSort for CondEqualities {
    type Ref = Sort<'static>;

    fn output_sort<'sort>(&'sort self) -> &'sort Self::Ref {
        COND_REF.as_ref()
    }
}

impl HasOutputSort for Eval {
    type Ref = Sort<'static>;
    fn output_sort<'sort>(&'sort self) -> &'sort Self::Ref {
        match self {
            Eval::Eval(e) | Eval::UnEval(e) => e.output_sort()
        }
    }
}

impl HasInputSorts for CondEqualities {
    type Ref = RcSort;

    fn input_sorts<'sort>(&'sort self) -> &'sort [Self::Ref] {
        
    }
}