use std::{rc::Rc, cell::RefCell, collections::HashMap};

use crate::formula::{
    builtins::types::{MSG_NAME, STEP_NAME},
    function::{self, Function},
    sort::Sort, formula::{RichFormula, Variable},
};
use core::fmt::Debug;

use super::step::Step;

#[derive(Hash)]
pub struct MemoryCell(Rc<InnerMemoryCell>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PreMemoryCell(Box<InnerMemoryCell>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct InnerMemoryCell {
    name: String,
    /// the arguments of the cell
    args: Vec<Sort>,
    /// the function used to refer to it
    /// 
    /// NB: this function takes one more argument of sort step
    function: Function,
    assignements: Vec<Assignement>
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Assignement {
    pub step: Step,
    // pub vars: Vec<Variable>, // those are the step's free variables
    /// all the relevant arguments, this means it doesn't have the last `step` argument
    /// 
    /// `args.len() == InnerMemoryCell::args.len()`
    pub args: Vec<RichFormula>,
    pub content: RichFormula
}

// impl

impl PreMemoryCell {
    pub fn new(name: String, function: Function) -> Self {
        assert!(function.get_output_sort().name() == MSG_NAME);

        let args = { // this is way more complicated than it should be...
            let tmp = function.get_input_sorts();
            let mut in_s = tmp.iter();
            let last = in_s.next_back();

            assert!(last.map(Sort::name) == Some(STEP_NAME));
            in_s.cloned().collect()
        }; // all of this to stop the borow of function

        let inner = InnerMemoryCell {
            name: name.to_owned(),
            args,
            function,
            assignements: vec![]
        };
        PreMemoryCell(Box::new(inner))
    }

    pub fn add_asignement(&mut self, a: Assignement) {
        assert_eq!(a.args.len(), self.0.args.len(), "wrong nnumber of arguments");
        self.0.assignements.push(a)
    }

    pub fn name(&self) -> &str {
        &self.0.name
    }

    pub fn args(&self) -> &Vec<Sort> {
        &self.0.args
    }

    pub fn function(&self) -> &Function {
        &self.0.function
    }
}

impl MemoryCell {
    pub fn name(&self) -> &str {
        &self.0.name
    }

    pub fn args(&self) -> &Vec<Sort> {
        &self.0.args
    }

    pub fn function(&self) -> &Function {
        &self.0.function
    }

    pub fn assignements(&self) -> &Vec<Assignement> {
        &self.0.assignements
    }
}

impl From<PreMemoryCell> for MemoryCell {
    fn from(m: PreMemoryCell) -> Self {
        Self(Rc::new(*m.0))
    }
}

// base impl

impl Debug for MemoryCell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Clone for MemoryCell {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl PartialEq for MemoryCell {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for MemoryCell {}

impl Ord for MemoryCell {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&Rc::as_ptr(&self.0), &Rc::as_ptr(&other.0))
    }
}

impl PartialOrd for MemoryCell {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.0.cmp(&other.0))
    }
}
