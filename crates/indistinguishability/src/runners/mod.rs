use std::fmt::Debug;
use std::path::Path;
use std::time::Duration;

use cryptovampire_smt::SolverKind;
use golgge::Dependancy;
use itertools::zip_eq;
use tempfile::NamedTempFile;
use tokio::fs::File;
use tokio::sync::RwLock;

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
    async fn try_run<'a>(&self, pbl: &Problem, query: &Path) -> anyhow::Result<Option<bool>>;

    async fn try_run_spin<'a>(&self, pbl: &Problem, query: &Path) -> anyhow::Result<bool> {
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
    pub vampire: Option<VampireExec>,
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
    async fn run_all(&self, pbl: &Problem, query: &FileSink<'_>) -> anyhow::Result<bool> {
        let Self { vampire } = self;
        tokio::select! {
            _ = to_timeout::<()>(pbl) => Ok(false),
            res = maybe_run(pbl, &query.files.vampire, vampire) => res
        }
    }

    pub fn run_to_dependancy(&self, pbl: &mut Problem, queries: &[Formula]) -> Dependancy {
        pbl.cache.smt.force_reset();
        pbl.find_temp_quantifiers(queries);

        for query in queries {
            let mut sink = FileSink::new(pbl, self);

            // z3 or cvc5 would set up some headers in the smt files (like chosing a theory & co)

            {
                // use the cache
                let FileSink { cache, files, .. } = &mut sink;
                for (c, f) in zip_eq(cache.as_mut(), files.as_mut()) {
                    use ::std::io::Write;
                    write!(f, "{c}").unwrap()
                }
            }

            pbl.add_smt(
                &mut Context {
                    query: query.clone(),
                    query_smt: query.as_smt(pbl).unwrap(),
                    using_cache: false,
                },
                &mut sink,
            );

            if pbl.config.keep_smt_files {
                for f in sink.files.as_ref() {
                    println!("save smt file to: {:?}", f.path())
                }
            }

            if !self.run_all(pbl, &sink).unwrap() {
                return Dependancy::impossible();
            }
        }

        Dependancy::axiom()
    }
}

//     /// Runs the SMT solver with the given query and converts the result to a `Dependancy`.
//     ///
//     /// If the query is proven true, it returns `Dependancy::axiom()`; otherwise, `Dependancy::impossible()`.
//     pub fn run_to_dependancy(&self, pbl: &mut Problem, query: MSmtFormula) -> Dependancy {
//         if let Some(true) = self.try_run(pbl, query).unwrap() {
//             Dependancy::axiom()
//         } else {
//             Dependancy::impossible()
//         }
//     }

//     /// Attempts to run the SMT solvers (regular and bounded Vampire) concurrently.
//     ///
//     /// It returns `Ok(Some(true))` if a proof is found, `Ok(Some(false))` if disproven,
//     /// `Ok(None)` if a timeout occurs, or `Err` if a solver error happens.
//     #[tokio::main]
//     pub async fn try_run(
//         &self,
//         pbl: &mut Problem,
//         query: MSmtFormula,
//     ) -> anyhow::Result<Option<bool>> {
//         let query = query.optimise();
//         if query.is_true() {
//             return Ok(Some(true));
//         } else if query.is_false() {
//             return Ok(Some(false));
//         }

//         let Self {
//             regular_vampire,
//             bounded_vapire,
//         } = self;

//         let pbl = SharedProblem(RwLock::new(pbl));

//         let start = std::time::Instant::now();
//         let res = tokio::select! {
//             x = regular_vampire.try_run_spin(&pbl, query.clone()) => x.map(Some),
//             x = bounded_vapire.try_run_spin(&pbl, query.clone()) => x.map(Some),
//             _ = tokio::time::sleep( pbl.0.read().await.config.vampire_timeout) => Ok(None)
//         };
//         {
//             let time = start.elapsed();
//             let mut pbl = pbl.0.write().await;
//             pbl.report.time_spent_in_vampire += time;
//             if let Ok(Some(true)) = res
//                 && pbl.report.max_vampire < time
//             {
//                 pbl.report.max_vampire = time;
//                 if pbl.config.trace {
//                     eprintln!("new longest vampire!")
//                 }
//             }
//         }
//         res
//     }
// }

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
    query: &Option<NamedTempFile>,
    r: &Option<R>,
) -> anyhow::Result<bool> {
    match (r.as_ref(), query.as_ref()) {
        (Some(x), Some(query)) => x.try_run_spin(pbl, query.path()).await,
        _ => never_end().await,
    }
}

/// A wrapper around `Problem` to allow shared mutable access across asynchronous tasks.
///
/// Differs from [crate::input::shared_problem::ShrProblem] in the sense that it's async.
struct SharedProblem<'a>(RwLock<&'a mut Problem>);

// impl<'a> SharedProblem<'a> {
//     /// Extends the given SMT prelude with the problem's SMT prelude.
//     ///
//     /// If the problem's SMT prelude has not been computed yet, it computes it.
//     pub async fn extend_smt_prelud(&self, rec: &mut Vec<MSmt>) {
//         // split here to avoid taking a lock if possible
//         if let Some(p) = self.0.read().await.maybe_get_smt_prelude() {
//             rec.extend_from_slice(p);
//         } else {
//             rec.extend_from_slice(self.0.write().await.get_smt_prelude());
//         }
//     }
// }
