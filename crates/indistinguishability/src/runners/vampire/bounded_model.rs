use crate::Problem;
use crate::runners::SmtSolver;
use crate::runners::vampire::{self, VampireExec, vampire_suboptions};

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
                        Cores(pbl.config.cores - 1),
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
    fn try_run(
        &self,
        pbl: &mut Problem,
        query: crate::MSmtFormula,
    ) -> anyhow::Result<Option<bool>> {
        self.0.run_smt_with_pbl(pbl, query).map(|x| x.map(|y| !y))
    }
}
