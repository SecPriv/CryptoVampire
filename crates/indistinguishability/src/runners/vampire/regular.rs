use crate::Problem;
use crate::runners::vampire::{VampireExec, vampire_suboptions};
use crate::runners::{SharedProblem, SmtSolver};

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
                        Cores(Ord::max(1, pbl.config.cores - 1)),
                        Mode(vampire_suboptions::Mode::Portfolio),
                        InputSyntax(vampire_suboptions::InputSyntax::SmtLib2),
                    ]
                })
                .build(),
        )
    }
}

impl SmtSolver for RegularVampire {
    async fn try_run<'a>(
        &self,
        pbl: &SharedProblem<'a>,
        query: crate::MSmtFormula,
    ) -> anyhow::Result<Option<bool>> {
        self.0.run_smt_with_pbl(pbl, query).await
    }
}
