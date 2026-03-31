use std::fmt::Debug;
use std::path::Path;
use std::time::Duration;

use cryptovampire_smt::SolverKind;
use golgge::Dependancy;
use itertools::zip_eq;
use tempfile::NamedTempFile;
use tokio::fs::File;
use tokio::sync::RwLock;
use utils::{econtinue_if, ereturn_if};

use crate::libraries::utils::{SmtOption, SmtSink};
use crate::problem::cache::Context;
use crate::runners::file_builder::FileSink;
use crate::runners::vampire::{VampireArg, VampireExec};
use crate::terms::Formula;
use crate::{MSmt, MSmtFormula, Problem};

pub(crate) mod vampire;

pub(crate) mod file_builder;

mod runner_spliter;
pub use runner_spliter::RunnerSplitter;

// /// A trait for SMT solvers.
trait Runner: Debug {
    /// Tries to prove .
    ///
    /// ## returns
    /// - `Err(_)` if the solver errored out (e.g., syntax error and such).
    /// - `Ok(None)` the solver didn't manage to prove nor disprove the query
    /// - `Ok(b)` with `b` true is proven, `false` otherwise
    async fn try_run(&self, pbl: &Problem, query: &Path) -> anyhow::Result<Option<bool>>;

    async fn try_run_spin(&self, pbl: &Problem, query: &Path) -> anyhow::Result<bool> {
        match self.try_run(pbl, query).await? {
            Some(x) => Ok(x),
            _ => never_end().await,
        }
    }

    fn mut_splitter<'a, U>(&self, spliter: &'a mut RunnerSplitter<U>) -> Option<&'a mut U>;

    fn get_sover_kind(&self) -> SolverKind;
}

/// A runner for SMT solvers, encapsulating different Vampire configurations.
#[derive(Debug, Clone)]
pub struct SmtRunner {
    // /// The regular Vampire solver instance.
    // regular_vampire: Option<RegularVampire>,
    // /// The bounded Vampire solver instance.
    // bounded_vapire: Option<BounededVampire>,
    vampire: Option<VampireExec>,
}

// impl<T: SmtSolver> SmtSolver for Option<T> {
//     async fn try_run<'a>(
//         &self,
//         pbl: &SharedProblem<'a>,
//         query: MSmtFormula,
//     ) -> anyhow::Result<Option<bool>> {
//         match self {
//             Some(x) => x.try_run(pbl, query).await,
//             None => never_end().await,
//         }
//     }
// }

impl SmtRunner {
    /// Creates a new `SmtRunner` instance, initializing the Vampire solvers.
    pub fn new(pbl: &Problem) -> Self {
        Self {
            // regular_vampire: (!pbl.config.disable_direct_vampire).then(|| RegularVampire::new(pbl)),
            // bounded_vapire: (!pbl.config.disable_fmc_vampire).then(|| BounededVampiVre::new(pbl)),
            vampire: (!pbl.config.disable_direct_vampire).then(|| {
                let x = pbl
                    .config
                    .vampire_forced_option
                    .clone()
                    .map(VampireArg::ForcedOptions);
                VampireExec::builder()
                    .timeout(pbl.config.vampire_timeout)
                    .default_args()
                    .extend_args(x)
                    .maybe_exe_location(pbl.config.vampire_path.clone())
                    .build()
            }),
        }
    }

    #[tokio::main]
    async fn run_all(&self, pbl: &mut Problem, query: &FileSink<'_>) -> anyhow::Result<bool> {
        let Self { vampire } = self;
        let start = std::time::Instant::now();
        let success = tokio::select! {
            _ = to_timeout::<()>(pbl) => Ok(false),
            res = maybe_run(pbl, query.vampire_file(), vampire) => res
        }?;
        let time = start.elapsed();

        pbl.report.add_smt_time(time, success);
        Ok(success)
    }

    pub fn run_to_dependancy(&self, pbl: &mut Problem, queries: &[Formula]) -> Dependancy {
        pbl.cache.smt.reset();
        pbl.find_temp_quantifiers(queries);

        let lock = pbl.cache.smt.lock();
        let mut using_cache = false;

        let mut sink = FileSink::new(pbl, self).unwrap();

        for query in queries {
            match query.try_evaluate() {
                Some(true) => continue,
                Some(false) => return Dependancy::impossible(),
                _ => {}
            }

            pbl.cache.smt.reset();
            sink.clear_files(pbl).unwrap();

            let query_smt = query.as_smt(pbl).unwrap().optimise();

            // z3 or cvc5 would set up some headers in the smt files (like chosing a theory & co)


            sink.write_cache().unwrap();

            pbl.add_smt(
                &Context {
                    query: query.clone(),
                    query_smt: query_smt.clone(),
                    using_cache,
                },
                &mut sink,
            );

            sink.extend_smt(
                pbl,
                &SmtOption {
                    depend_on_context: true,
                },
                [MSmt::AssertNot(query_smt), MSmt::CheckSat],
            );


            if pbl.config.keep_smt_files {
                for f in sink.files.as_ref() {
                    println!("save smt file to: {:?}", f.path())
                }
            }

            if !self.run_all(pbl, &sink).unwrap() {
                return Dependancy::impossible();
            }

            using_cache = true;
        }

        drop(lock);

        Dependancy::axiom()
    }
}

async fn never_end<T>() -> T {
    loop {
        tokio::time::sleep(Duration::from_secs(1)).await
    }
}

async fn to_timeout<T>(pbl: &Problem) -> Option<T> {
    let timeout = pbl.config.vampire_timeout;
    tokio::time::sleep(timeout).await;
    None
}

async fn maybe_run<R: Runner>(
    pbl: &Problem,
    query: Option<&Path>,
    r: &Option<R>,
) -> anyhow::Result<bool> {
    match (r.as_ref(), query) {
        (Some(x), Some(query)) => x.try_run_spin(pbl, query).await,
        (None, None) => never_end().await,
        _ => unreachable!(),
    }
}
