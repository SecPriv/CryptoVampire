use egg::RecExpr;
use itertools::Itertools;

use crate::Lang;

use super::Step;
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Protocol {
    pub name: RecExpr<Lang>,
    pub steps: Vec<Step>,
}


impl Protocol {
    /// Two protocols are compatible if they have the same step names
    pub fn are_compatible(Protocol { steps:steps_a, .. }:&Protocol, Protocol {  steps:steps_b ,..}:&Protocol) -> bool {
        let mut steps_a = steps_a.iter().map(|s| &s.id).collect_vec();
        let mut steps_b = steps_b.iter().map(|s| &s.id).collect_vec();
        steps_a.sort_unstable();
        steps_b.sort_unstable();
        steps_a == steps_b
    }
}