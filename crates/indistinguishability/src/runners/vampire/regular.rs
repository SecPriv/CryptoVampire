use crate::Problem;
use crate::runners::vampire::{VampireExec, vampire_suboptions};
use crate::runners::{SharedProblem, SmtSolver};

/// A wrapper around `VampireExec` configured for regular SMT solving.
#[derive(Debug, Clone)]
pub struct RegularVampire(VampireExec);

impl RegularVampire {
    /// Creates a new `RegularVampire` instance with default regular SMT solving arguments.
    pub fn new(pbl: &Problem) -> Self {
        Self(
            VampireExec::builder()
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
    /// Attempts to run the regular Vampire solver with the given SMT query.
    ///
    /// Returns `Ok(Some(true))` if the query is proven, `Ok(Some(false))` if disproven,
    /// or `Err` if a solver error occurs.
    async fn try_run<'a>(
        &self,
        pbl: &SharedProblem<'a>,
        query: crate::MSmtFormula,
    ) -> anyhow::Result<Option<bool>> {
        self.0.run_smt_with_pbl(pbl, query).await
    }
}
