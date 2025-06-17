use cryptovampire_macros::smt;
use itertools::Itertools;

use crate::{MSmtFormula, terms::Function};

use super::Step;
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Protocol {
    name: Function,
    steps: Vec<Step>,
}

impl Protocol {
    pub fn new(name: Function) -> Self {
        Self {
            name,
            steps: vec![],
        }
    }

    /// Two protocols are compatible if they have the same step names
    pub fn are_compatible(
        Protocol { steps: steps_a, .. }: &Protocol,
        Protocol { steps: steps_b, .. }: &Protocol,
    ) -> bool {
        let mut steps_a = steps_a.iter().map(|s| &s.id).collect_vec();
        let mut steps_b = steps_b.iter().map(|s| &s.id).collect_vec();
        steps_a.sort_unstable();
        steps_b.sort_unstable();
        steps_a == steps_b
    }

    pub fn add_step(&mut self, step: Step) {
        assert!(step.valid());
        self.steps.push(step)
    }

    #[inline]
    pub fn steps(&self) -> &[Step] {
        &self.steps
    }

    #[inline]
    pub fn name(&self) -> &Function {
        &self.name
    }

    pub(crate) fn as_smt(&self) -> MSmtFormula {
        let name = self.name();
        smt!(name)
    }
}
