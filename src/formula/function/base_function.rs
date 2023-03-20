use core::slice::SlicePattern;

use crate::formula::sort::Sort;

use super::function_like::{HasInputSorts, Named, HasOutputSort};

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BaseFunction<'a> {
    pub name: String,
    pub args: Box<[Sort<'a>]>,
    pub output: Sort<'a>,
    pub info: Information,
}

impl<'a> HasInputSorts<'a> for BaseFunction<'a> {
    fn input_sorts(&self) -> &[Sort<'a>] {
        self.input_sorts().as_slice()
    }
}

impl<'a> HasOutputSort<'a> for BaseFunction<'a> {
    fn output_sort(&self) -> Sort<'a> {
        self.output
    }
}

impl<'a> Named for BaseFunction<'a> {
    fn name(&self) -> &str {
        &self.name
    }
}


#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Information {
    // pub is_term_algebra: bool,
    pub user_generated: bool
}
