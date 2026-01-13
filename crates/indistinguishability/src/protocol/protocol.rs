use bon::Builder;
use itertools::Itertools;

use super::Step;
use crate::terms::Function;
use crate::{MSmtFormula, smt};
/// A protocol to be proven
#[derive(Debug, PartialEq, Eq, Clone, Builder)]
pub struct Protocol {
    /// The name of the protocol
    /// The name of the protocol
    name: Function,
    /// The steps of the protocol
    #[builder(with = <_>::from_iter, default = vec![Step::default()])]
    steps: Vec<Step>,
}

impl Protocol {
    /// Creates a new protocol with the given name
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

    /// Returns the steps of the protocol
    #[inline]
    pub fn steps(&self) -> &[Step] {
        &self.steps
    }

    /// Returns the name of the protocol
    #[inline]
    pub fn name(&self) -> &Function {
        &self.name
    }

    /// Converts the protocol's name into an SMT formula.
    pub(crate) fn as_smt(&self) -> MSmtFormula {
        let name = self.name();
        smt!(name)
    }

    /// Adds a new step to the protocol.
    ///
    /// # Panics
    ///
    /// Panics if the provided step is not valid (i.e., its free variables are not contained in its step variables).
    pub(crate) fn add_step(&mut self, step: Step) -> &mut Step {
        assert!(step.valid());
        self.steps.push(step);
        self.steps.last_mut().unwrap()
    }

    /// Returns a mutable reference to the step at the given index
    pub fn step_mut(&mut self, idx: usize) -> Option<&mut Step> {
        self.steps.get_mut(idx)
    }

    pub(crate) fn truncate_steps(&mut self, n: usize) {
        self.steps.truncate(n);
    }
}
