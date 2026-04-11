use std::fmt::Debug;
use std::path::Path;
use std::time::Duration;

use cryptovampire_smt::SolverKind;
use golgge::Dependancy;
use itertools::{Itertools, zip_eq};
use tempfile::NamedTempFile;
use tokio::fs::File;
use tokio::sync::RwLock;
use utils::{econtinue_if, ereturn_if, implvec};

use crate::libraries::utils::{SmtOption, SmtSink};
use crate::problem::cache::Context;
use crate::runners::cvc5::Cvc5Exec;
use crate::runners::file_builder::FileSink;
use crate::runners::vampire::{VampireArg, VampireExec};
use crate::runners::z3::Z3Exec;
use crate::terms::Formula;
use crate::{MSmt, MSmtFormula, Problem};

pub(crate) mod cvc5;
pub(crate) mod vampire;
pub(crate) mod z3;

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

/// A runner for SMT solvers, encapsulating different solver configurations.
#[derive(Debug, Clone)]
pub struct SmtRunner {
    vampire: Option<VampireExec>,
    z3: Option<Z3Exec>,
    cvc5: Option<Cvc5Exec>,
}

impl SmtRunner {
    fn calculate_core_distribution() -> (u64, bool, bool) {
        let total_cores = num_cpus::get() as u64;
        let z3_enabled = true;
        let cvc5_enabled = true;

        let other_solvers = [z3_enabled, cvc5_enabled].iter().filter(|&&x| x).count() as u64;

        let vampire_cores = if other_solvers > 0 {
            total_cores.saturating_sub(other_solvers)
        } else {
            total_cores
        };

        (vampire_cores, z3_enabled, cvc5_enabled)
    }

    /// Creates a new `SmtRunner` instance, initializing the solvers.
    pub fn new(pbl: &Problem) -> Self {
        let disable = pbl.config.disable_direct_vampire;

        let (vampire_cores, _, _) = Self::calculate_core_distribution();

        Self {
            vampire: (!disable).then(|| {
                VampireExec::builder()
                    .default_args_with_cores(vampire_cores)
                    .maybe_exe_location(pbl.config.vampire_path.clone())
                    .build()
            }),
            z3: (!disable).then(|| {
                Z3Exec::builder()
                    .default_args()
                    .maybe_exe_location(pbl.config.z3_path.clone())
                    .build()
            }),
            cvc5: (!disable).then(|| {
                Cvc5Exec::builder()
                    .default_args()
                    .maybe_exe_location(pbl.config.cvc5_path.clone())
                    .build()
            }),
        }
    }

    #[tokio::main]
    async fn run_all(&self, pbl: &mut Problem, query: &FileSink<'_>) -> anyhow::Result<bool> {
        let Self { vampire, z3, cvc5 } = self;
        let start = std::time::Instant::now();

        let (file, success) = tokio::select! {
            _ = to_timeout::<()>(pbl) => Ok((None, false)),
            res = run_all_solvers(pbl, query, vampire, z3, cvc5) => res
        }?;
        let time = start.elapsed();

        pbl.report
            .add_smt_time(pbl.config.keep_smt_files, time, file, success);
        Ok(success)
    }

    pub fn iter_run_to_dependancy(
        &self,
        pbl: &mut Problem,
        queries: implvec!(Formula),
    ) -> Dependancy {
        let queries = queries
            .into_iter()
            .flat_map(Formula::into_iter_conjunction)
            .collect_vec();

        {
            let this = &self;
            let queries: &[Formula] = &queries;
            pbl.cache.smt.reset();
            pbl.find_temp_quantifiers(queries);

            let lock = pbl.cache.smt.lock();
            let mut using_cache = false;

            let mut sink = FileSink::new(pbl, this).unwrap();

            for query in queries {
                match query.try_evaluate() {
                    Some(true) => continue,
                    Some(false) => return Dependancy::impossible(),
                    _ => {}
                }

                pbl.cache.smt.reset();
                if using_cache {
                    sink.clear_files(pbl).unwrap();
                }

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
                        println!("saved smt file to: {:?}", f.path())
                    }
                }

                if !this.run_all(pbl, &sink).unwrap() {
                    return Dependancy::impossible();
                }

                using_cache = true;
            }

            drop(lock);

            Dependancy::axiom()
        }
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

async fn run_all_solvers<'a>(
    pbl: &Problem,
    query: &'a FileSink<'_>,
    vampire: &Option<VampireExec>,
    z3: &Option<Z3Exec>,
    cvc5: &Option<Cvc5Exec>,
) -> anyhow::Result<(Option<&'a Path>, bool)> {
    let timeout_fut = to_timeout::<()>(pbl);
    tokio::pin!(timeout_fut);

    let vampire_fut = async {
        if let (Some(solver), Some(file)) = (vampire, query.vampire_file()) {
            solver.run(pbl, file).await
        } else {
            never_end().await
        }
    };
    tokio::pin!(vampire_fut);

    let z3_fut = async {
        if let (Some(solver), Some(file)) = (z3, query.z3_file()) {
            solver.run(pbl, file).await
        } else {
            never_end().await
        }
    };
    tokio::pin!(z3_fut);

    let cvc5_fut = async {
        if let (Some(solver), Some(file)) = (cvc5, query.cvc5_file()) {
            solver.run(pbl, file).await
        } else {
            never_end().await
        }
    };
    tokio::pin!(cvc5_fut);

    loop {
        tokio::select! {
            _ = &mut timeout_fut => {
                return Ok((None, false));
            }

            res = &mut vampire_fut => {
                match res {
                    Ok(true) => return Ok((query.vampire_file(), true)),
                    Ok(false) => {}
                    Err(e) => {
                        panic!(
                            "Vampire crashed with error: {}\nThis likely indicates a problem with the SMT file or \
                             solver configuration.",
                            e
                        );
                    }
                }
            }

            res = &mut z3_fut => {
                match res {
                    Ok(true) => return Ok((query.z3_file(), true)),
                    Ok(false) => {}
                    Err(e) => {
                        panic!(
                            "Z3 crashed with error: {}\nThis likely indicates a problem with the SMT file or \
                             solver configuration.",
                            e
                        );
                    }
                }
            }

            res = &mut cvc5_fut => {
                match res {
                    Ok(true) => return Ok((query.cvc5_file(), true)),
                    Ok(false) => {}
                    Err(e) => {
                        panic!(
                            "CVC5 crashed with error: {}\nThis likely indicates a problem with the SMT file or \
                             solver configuration.",
                            e
                        );
                    }
                }
            }
        }
    }
}

async fn maybe_run<'a, R: Runner>(
    pbl: &Problem,
    query: Option<&'a Path>,
    r: &Option<R>,
) -> anyhow::Result<(Option<&'a Path>, bool)> {
    match (r.as_ref(), query) {
        (Some(x), Some(query)) => Ok((Some(query), x.try_run_spin(pbl, query).await?)),
        (None, None) => never_end().await,
        _ => unreachable!(),
    }
}
