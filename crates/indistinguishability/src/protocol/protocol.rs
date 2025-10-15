use bon::Builder;
use itertools::Itertools;

use super::Step;
use crate::{smt, MSmtFormula};
use crate::terms::Function;
#[derive(Debug, PartialEq, Eq, Clone, Builder)]
pub struct Protocol {
    name: Function,
    #[builder(with = <_>::from_iter, default = vec![Step::builder().build().unwrap()])]
    steps: Vec<Step>,
}

impl Protocol {
    pub fn new(name: Function) -> Self {
        Self::builder().name(name).build()
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

    pub(crate) fn add_step(&mut self, step: Step) -> &mut Step {
        assert!(step.valid());
        self.steps.push(step);
        self.steps.last_mut().unwrap()
    }

    pub fn step_mut(&mut self, idx: usize) -> Option<&mut Step> {
        self.steps.get_mut(idx)
    }
}
