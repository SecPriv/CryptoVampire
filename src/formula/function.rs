use std::sync::Arc;

use super::sort::Sort;
use core::fmt::Debug;

#[derive(Hash)]
pub struct Function(Arc<InnerFunction>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct InnerFunction {
    name: String,
    input_sorts: Vec<Sort>,
    output_sort: Sort,
}

impl Debug for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Clone for Function {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Function {}

impl Ord for Function {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&Arc::as_ptr(&self.0), &Arc::as_ptr(&other.0))
    }
}

impl PartialOrd for Function {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl Function {
    pub fn new(name: &str, input_sorts: Vec<Sort>, output_sort: Sort) -> Self {
        Function(Arc::new(InnerFunction {
            name: name.to_owned(),
            input_sorts,
            output_sort,
        }))
    }

    pub fn arity(&self) -> usize {
        self.0.input_sorts.len()
    }

    pub fn get_input_sorts(&self) -> &[Sort] {
        self.0.as_ref().input_sorts.as_slice()
    }

    pub fn get_output_sort(&self) -> &Sort {
        &self.0.output_sort
    }
}
