use crate::Problem;
use crate::runners::SmtSolver;
use crate::runners::vampire::{self, VampireExec, vampire_suboptions};

#[derive(Debug, Clone)]
pub struct RegularVampire(VampireExec);

impl RegularVampire {
    pub fn new(pbl: &Problem) -> Self {
        Self(
            VampireExec::builder()
                .with_pbl(pbl)
                .extend_args({
                    use super::VampireArg::*;
                    [
                        Cores(pbl.config.cores - 1),
                        Mode(vampire_suboptions::Mode::Portfolio),
                        InputSyntax(vampire_suboptions::InputSyntax::SmtLib2),
                    ]
                })
                .build(),
        )
    }
}

impl SmtSolver for RegularVampire {
    fn try_run(&self, pbl: &mut Problem, query: crate::MSmtFormula) -> anyhow::Result<Option<bool>> {
        self.0.run_smt_with_pbl(pbl, query)
    }
}