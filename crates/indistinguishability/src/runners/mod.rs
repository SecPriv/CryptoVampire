use std::fmt::Debug;
use std::time::Duration;

use golgge::Dependancy;
use tokio::sync::RwLock;

use crate::runners::vampire::{BounededVampire, RegularVampire};
use crate::{MSmt, MSmtFormula, Problem};

pub(crate) mod vampire;

/// A trait for SMT solvers.
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

/// A runner for SMT solvers, encapsulating different Vampire configurations.
#[derive(Debug, Clone)]
pub struct SmtRunner {
    /// The regular Vampire solver instance.
    regular_vampire: Option<RegularVampire>,
    /// The bounded Vampire solver instance.
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
    /// Creates a new `SmtRunner` instance, initializing the Vampire solvers.
    pub fn new(pbl: &Problem) -> Self {
        Self {
            regular_vampire: Some(RegularVampire::new(pbl)),
            bounded_vapire: Some(BounededVampire::new(pbl)),
        }
    }

    /// Runs the SMT solver with the given query and converts the result to a `Dependancy`.
    ///
    /// If the query is proven true, it returns `Dependancy::axiom()`; otherwise, `Dependancy::impossible()`.
    pub fn run_to_dependancy(&self, pbl: &mut Problem, query: MSmtFormula) -> Dependancy {
        if let Some(true) = self.try_run(pbl, query).unwrap() {
            Dependancy::axiom()
        } else {
            Dependancy::impossible()
        }
    }

    /// Attempts to run the SMT solvers (regular and bounded Vampire) concurrently.
    ///
    /// It returns `Ok(Some(true))` if a proof is found, `Ok(Some(false))` if disproven,
    /// `Ok(None)` if a timeout occurs, or `Err` if a solver error happens.
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

        let start = std::time::Instant::now();
        let res = tokio::select! {
            x = regular_vampire.try_run_spin(&pbl, query.clone()) => x.map(Some),
            x = bounded_vapire.try_run_spin(&pbl, query.clone()) => x.map(Some),
            _ = tokio::time::sleep( pbl.0.read().await.config.vampire_timeout) => Ok(None)
        };
        {
            let time = start.elapsed();
            let mut pbl = pbl.0.write().await;
            pbl.report.time_spent_in_vampire += time;
            if let Ok(Some(true)) = res
                && pbl.report.max_vampire < time
            {
                pbl.report.max_vampire = time;
                if pbl.config.trace {
                    eprintln!("new longest vampire!")
                }
            }
        }
        res
    }
}

async fn never_end<T>() -> T {
    loop {
        tokio::time::sleep(Duration::from_secs(1)).await
    }
}

/// A wrapper around `Problem` to allow shared mutable access across asynchronous tasks.
struct SharedProblem<'a>(RwLock<&'a mut Problem>);

impl<'a> SharedProblem<'a> {
    /// Extends the given SMT prelude with the problem's SMT prelude.
    ///
    /// If the problem's SMT prelude has not been computed yet, it computes it.
    pub async fn extend_smt_prelud(&self, rec: &mut Vec<MSmt>) {
        if let Some(p) = self.0.read().await.maybe_get_smt_prelude() {
            rec.extend_from_slice(p);
        } else {
            rec.extend_from_slice(self.0.write().await.get_smt_prelude());
        }
    }

    pub async fn keep_smt_files(&self) -> bool {
        self.0.read().await.config.keep_smt_files
    }
}
