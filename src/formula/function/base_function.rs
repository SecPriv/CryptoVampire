

use crate::formula::sort::{RcSort, Sort};

use super::function_like::{HasInputSorts, HasOutputSort, Named};

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BaseFunction {
    pub name: String,
    pub args: Box<[RcSort]>,
    pub output: RcSort,
    pub info: Information,
}

impl HasInputSorts for BaseFunction {
    type Ref = RcSort;

    fn input_sorts<'sort>(&'sort self) -> &'sort [Self::Ref] {
        self.args.as_slice()
    }
}

impl HasOutputSort for BaseFunction {
    type Ref = RcSort;

    fn output_sort<'sort>(&'sort self) -> &'sort Self::Ref {
        &self.output
    }
}

impl Named for BaseFunction {
    fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Information {
    // pub is_term_algebra: bool,
    pub user_generated: bool,
}
