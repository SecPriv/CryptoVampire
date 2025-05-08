use super::Step;
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Protocol<L> {
    steps: Vec<Step<L>>,
}

impl<L> Protocol<L> {
    fn steps(&self) -> &[Step<L>] {
        &self.steps
    }

    fn steps_mut(&mut self) -> &mut Vec<Step<L>> {
        &mut self.steps
    }
}
