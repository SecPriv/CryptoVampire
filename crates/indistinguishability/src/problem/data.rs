use crate::Problem;
use crate::runners::SmtRunner;

#[derive(Default)]
pub struct ProblemData {
    pub vampire_exec: Option<SmtRunner>,
}

impl Problem {
    pub fn get_or_init_smt_runner(&mut self) -> &SmtRunner {
        if self.data.vampire_exec.is_none() {
            self.data.vampire_exec = Some(SmtRunner::new(self));
            self.data.vampire_exec.as_ref().unwrap()
        } else {
            self.data.vampire_exec.as_ref().unwrap()
        }
    }
}
