use crate::Problem;

#[derive(Debug, Clone, Copy)]
pub struct Checkpoint {
    extra_rules: usize,
    extra_rewrite: usize,
    extra_smt: usize,
    steps: usize,
    constrains: usize,
    temporary: (usize, usize),
    public_terms: usize,
}

impl Checkpoint {
    fn new(pbl: &Problem) -> Self {
        Checkpoint {
            extra_rules: pbl.extra_rules.len(),
            extra_rewrite: pbl.extra_rewrite.len(),
            extra_smt: pbl.extra_smt.len(),
            steps: pbl.protocols[0].steps().len(),
            constrains: pbl.constrains.len(),
            temporary: pbl.functions().temporary_len(),
            public_terms: pbl.public_terms.len(),
        }
    }

    /// restores `pbl` to the state 'saved' by `self`
    fn restore(&self, pbl: &mut Problem) {
        for ptcl in &mut pbl.protocols {
            ptcl.truncate_steps(self.steps);
        }

        pbl.extra_rewrite_mut().truncate(self.extra_rewrite);
        pbl.extra_rules_mut().truncate(self.extra_rules);
        pbl.extra_smt_mut().truncate(self.extra_smt);
        pbl.constrains.truncate(self.constrains);
        pbl.clear_smt_prelude();
        pbl.public_terms.truncate(self.public_terms);
        // pbl.functions_mut().truncate_temporary(self.temporary);
    }

    fn reset_to(&self, pbl: &mut Problem) {
        self.restore(pbl);
        pbl.current_step = None;
    }
}

impl Problem {
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint::new(self)
    }

    pub fn reset_to(&mut self, chck: &Checkpoint) {
        chck.reset_to(self);
    }
}
