use std::fmt::Debug;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Duration;

use golgge::Dependancy;
use tokio::sync::RwLock;

use crate::runners::vampire::{BounededVampire, RegularVampire};
use crate::{MSmt, MSmtFormula, Problem};

pub(crate) mod vampire;

trait SmtSolver: Debug {
    /// Tries to prove .
    ///
    /// ## returns
    /// - `Err(_)` if the solver errored out (e.g., syntax error and such).
    /// - `Ok(None)` the solver didn't manage to prove nor disprove the query
    /// - `Ok(b)` with `b` true is proven, `false` otherwise
    async fn try_run<'a>(
        &self,
        pbl: &SharedProblem<'a>,
        query: MSmtFormula,
    ) -> anyhow::Result<Option<bool>>;

    async fn try_run_spin<'a>(
        &self,
        pbl: &SharedProblem<'a>,
        query: MSmtFormula,
    ) -> anyhow::Result<bool> {
        match self.try_run(pbl, query).await? {
            Some(x) => Ok(x),
            _ => never_end().await,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SmtRunner {
    regular_vampire: Option<RegularVampire>,
    bounded_vapire: Option<BounededVampire>,
}

impl<T: SmtSolver> SmtSolver for Option<T> {
    async fn try_run<'a>(
        &self,
        pbl: &SharedProblem<'a>,
        query: MSmtFormula,
    ) -> anyhow::Result<Option<bool>> {
        match self {
            Some(x) => x.try_run(pbl, query).await,
            None => never_end().await,
        }
    }
}

impl SmtRunner {
    pub fn new(pbl: &Problem) -> Self {
        Self {
            regular_vampire: Some(RegularVampire::new(pbl)),
            bounded_vapire: Some(BounededVampire::new(pbl)),
        }
    }

    pub fn run_to_dependancy(&self, pbl: &mut Problem, query: MSmtFormula) -> Dependancy {
        if let Some(true) = self.try_run(pbl, query).unwrap() {
            Dependancy::axiom()
        } else {
            Dependancy::impossible()
        }
    }

    #[tokio::main]
    pub async fn try_run(
        &self,
        pbl: &mut Problem,
        query: MSmtFormula,
    ) -> anyhow::Result<Option<bool>> {
        let Self {
            regular_vampire,
            bounded_vapire,
        } = self;

        let pbl = SharedProblem(RwLock::new(pbl));

        tokio::select! {
            x = regular_vampire.try_run_spin(&pbl, query.clone()) => x.map(Some),
            x = bounded_vapire.try_run_spin(&pbl, query.clone()) => x.map(Some),
            _ = tokio::time::sleep( pbl.0.read().await.config.vampire_timeout) => Ok(None)
        }
    }
}

async fn never_end<T>() -> T {
    loop {
        tokio::time::sleep(Duration::from_secs(1)).await
    }
}

struct SharedProblem<'a>(RwLock<&'a mut Problem>);

impl<'a> SharedProblem<'a> {
    pub async fn extend_smt_prelud(&self, rec: &mut Vec<MSmt>) {
        if let Some(p) = self.0.read().await.maybe_get_smt_prelude() {
            rec.extend_from_slice(p);
        } else {
            rec.extend_from_slice(self.0.write().await.get_smt_prelude());
        }
    }
}
