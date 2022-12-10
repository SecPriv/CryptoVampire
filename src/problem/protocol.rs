use core::fmt::Debug;
use std::{collections::HashMap, sync::Arc};

use crate::formula::{
    formula::{Formula, CNF},
    function::Function,
    sort::Sort,
};

#[derive(Debug)]
pub struct Protocol {
    steps: HashMap<String, Step>,
    functions: HashMap<String, Function>,
    sorts: Vec<Sort>,
}

impl Protocol {
    pub fn new<I, J, K>(steps: I, functions: J, sorts: K) -> Self
    where
        I: Iterator<Item = Step>,
        J: Iterator<Item = Function>,
        K: Iterator<Item = Sort>,
    {
        Self {
            steps: steps.map(|s| (s.name().to_owned(), s)).collect(),
            functions: functions.map(|f| (f.name().to_owned(), f)).collect(),
            sorts: sorts.collect(),
        }
    }
}

#[derive(Hash)]
pub struct Step(Arc<InnerStep>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct InnerStep {
    name: String,
    parameters: Vec<Sort>,
    condition: CNF,
    message: Formula,
}

impl Step {
    pub fn new(name: &str, parameters: Vec<Sort>, condition: CNF, message: Formula) -> Self {
        Self(Arc::new(InnerStep {
            name: name.to_owned(),
            parameters,
            condition,
            message,
        }))
    }

    pub fn name(&self) -> &str {
        &self.0.name
    }
}

impl Debug for Step {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Clone for Step {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl PartialEq for Step {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Step {}

impl Ord for Step {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&Arc::as_ptr(&self.0), &Arc::as_ptr(&other.0))
    }
}

impl PartialOrd for Step {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.0.cmp(&other.0))
    }
}
