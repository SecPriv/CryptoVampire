use crate::Problem;
use crate::runners::vampire::{self, VampireExec, vampire_suboptions};
use crate::runners::{SharedProblem, SmtSolver};

#[derive(Debug, Clone)]
pub struct BounededVampire(VampireExec);

impl BounededVampire {
    pub fn new(pbl: &Problem) -> Self {
        Self(
            VampireExec::builder()
                .with_pbl(pbl)
                .extend_args({
                    use super::VampireArg::*;
                    [
                        InputSyntax(vampire_suboptions::InputSyntax::SmtLib2),
                        SaturationAlgorithm(vampire_suboptions::SaturationAlgorithm::FiniteModel),
                    ]
                })
                .success_verification("Termination reason: Satisfiable\n")
                .build(),
        )
    }
}

impl SmtSolver for BounededVampire {
    async fn try_run<'a>(
        &self,
        pbl: &SharedProblem<'a>,
        query: crate::MSmtFormula,
    ) -> anyhow::Result<Option<bool>> {
        self.0
            .run_smt_with_pbl(pbl, query)
            .await
            .map(|x| x.map(|y| !y))
    }
}
