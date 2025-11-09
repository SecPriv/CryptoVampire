use super::*;
use crate::protocol::Step;
use crate::terms::Function;
use itertools::Itertools;
use std::num::NonZeroUsize;
use utils::implvec;

impl Problem {
    /// Push steps to all protocols, returns a mutable pointer to those steps
    ///
    /// The ith steps is pushed to the ith protocol
    ///
    /// # Panics
    ///
    /// If the number if steps is different from the number of protocol or they use different [Function]
    pub fn push_steps(&mut self, steps: implvec!(Step)) -> Vec<&mut Step> {
        let steps = steps
            .into_iter()
            .zip_eq(&mut self.protocols)
            .map(|(s, p)| p.add_step(s))
            .collect_vec();
        assert!(
            steps.iter().map(|s| &s.id).all_equal(),
            "The steps should all have the same name"
        );
        steps
    }

    /// Returns an iterator over the steps of the first protocol
    pub fn steps(&self) -> Option<impl Iterator<Item = Function> + use<'_>> {
        Some(
            self.protocols()
                .first()?
                .steps()
                .iter()
                .map(|Step { id, .. }| id.clone()),
        )
    }

    /// Returns the number of steps in the first protocol
    ///
    /// # Panics
    ///
    /// This function will panic if the first protocol has no steps.
    pub fn num_steps(&self) -> Option<NonZeroUsize> {
        let n = self.protocols().first()?.steps().len();
        let n = NonZeroUsize::new(n)
            .expect("a protocol has no steps, a protocol should always at least have an INIT step");
        Some(n)
    }
    /// returns the [Function] associated to the `index`th [Step] if it exists
    pub fn get_step_name(&self, index: usize) -> Option<&Function> {
        self.protocols().first()?.steps().get(index).map(|s| &s.id)
    }

    /// Returns a reference to the current step in the problem's execution, if any.
    #[allow(dead_code)]
    pub(crate) fn current_step(&self) -> Option<&CurrentStep> {
        self.current_step.as_ref()
    }
}
