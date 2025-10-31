use std::fmt::Display;
use std::sync::Arc;

use itertools::Itertools;

use crate::formula::formula::ARichFormula;
use crate::formula::variable::Variable;
use crate::problem::step::Step;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignement<'bump> {
    pub step: Step<'bump>,
    // pub vars: Vec<Variable>, // those are the step's free variables
    /// all the relevant arguments, this means it doesn't have the last `step` argument
    ///
    /// `args.len() == InnerMemoryCell::args.len()`
    pub args: Arc<[ARichFormula<'bump>]>,
    pub content: ARichFormula<'bump>,
    pub fresh_vars: Arc<[Variable<'bump>]>,
}

impl<'bump> Display for Assignement<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let step = self.step.name();
        let args = self.args.iter().map(|a| a.to_string()).join(", ");
        let content = self.content.to_string();
        let fresh_vars = self.fresh_vars.iter().map(|a| a.to_string()).join(", ");
        // write!(f, r"{")?;
        write!(
            f,
            "{{step: {step}, args: [{args}], content: {content}, fresh_vars: [{fresh_vars}]}}"
        )
    }
}
