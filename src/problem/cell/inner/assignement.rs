use std::sync::Arc;

use crate::{formula::formula::ARichFormula, problem::step::Step};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignement<'bump> {
    pub step: Step<'bump>,
    // pub vars: Vec<Variable>, // those are the step's free variables
    /// all the relevant arguments, this means it doesn't have the last `step` argument
    ///
    /// `args.len() == InnerMemoryCell::args.len()`
    pub args: Arc<[ARichFormula<'bump>]>,
    pub content: ARichFormula<'bump>,
}
