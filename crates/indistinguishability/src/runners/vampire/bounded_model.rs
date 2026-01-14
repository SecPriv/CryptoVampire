use crate::Problem;
use crate::runners::vampire::{VampireExec, vampire_suboptions};
use crate::runners::{SharedProblem, SmtSolver};

/// A wrapper around `VampireExec` configured for bounded model checking.
#[derive(Debug, Clone)]
pub struct BounededVampire(VampireExec);

impl BounededVampire {
    /// Creates a new `BounededVampire` instance with default bounded model checking arguments.
    pub fn new(_pbl: &Problem) -> Self {
        Self(
            VampireExec::builder()
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
    /// Attempts to run the bounded Vampire solver with the given SMT query.
    ///
    /// Returns `Ok(Some(true))` if the query is satisfiable (model found),
    /// `Ok(Some(false))` if unsatisfiable, or `Err` if a solver error occurs.
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
