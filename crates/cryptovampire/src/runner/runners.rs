use std::convert::Infallible;
use std::fmt::Display;
use std::io;
use std::num::NonZeroU32;
use std::path::Path;
use std::process::Command;
use std::sync::Arc;
use std::sync::mpsc::{Receiver, Sender, channel};
use std::thread::{self, ScopedJoinHandle};
use std::time::Duration;

use itertools::{Itertools, chain};
use log::{debug, trace};
use shared_child::SharedChild;
use thiserror::Error;

use super::dyn_traits::{self, DynRunner};
use super::z3::Z3Runner;
use super::{RunnerHandler, VampireArg, VampireExec};
use crate::environement::environement::{EnabledSolvers, Environement, SolverConfig};
use crate::error::{BaseError, CVContext};
use crate::problem::Problem;
use crate::runner::{RunnerError, RunnerOut};

#[derive(Debug, Clone)]
pub struct Runners {
    pub vampire: Option<VampireExec>,
    pub z3: Option<Z3Runner>,
    pub cvc5: Option<Infallible>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize)]
pub struct RunnerResult {
    num_tries: u32,
}

impl RunnerResult {
    pub fn num_tries(&self) -> u32 {
        self.num_tries
    }
}

impl Display for RunnerResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "proven in {:} tries.", self.num_tries())
    }
}

impl Runners {
    pub fn all_empty(&self) -> bool {
        self.vampire.is_none() && self.z3.is_none() && self.cvc5.is_none()
    }

    /// Automatically runs `pbl` using the [Runner] available in [self]
    ///
    /// If it succeeds it returns some information about the succeding solver.
    pub fn autorun<'bump>(
        self,
        env: &Environement<'bump>,
        pbl: &mut Problem<'bump>,
        ntimes: Option<NonZeroU32>,
        save_to: Option<&Path>,
    ) -> crate::Result<RunnerResult> {
        // ensure!((), !self.all_empty(), "no solver to run :'(");
        if self.all_empty() {
            return RunnerError::nothing_to_do("no solvers to run :'(").no_location();
        }
        let n: u32 = ntimes.map(NonZeroU32::get).unwrap_or(u32::MAX);

        let Runners { vampire, z3, .. } = self;

        let v = vampire.map(|v| dyn_traits::RunnerAndDiscoverer::Discoverer(Box::new(v)));
        let z3 = z3.map(|v| dyn_traits::RunnerAndDiscoverer::Runner(Box::new(v)));
        let runners = [v, z3].into_iter().flatten().collect_vec();

        for i in 1..=n {
            debug!("running {i:}/{n:}");

            let res = autorun_many(env, pbl, save_to, &runners)?;

            match res {
                RunnerOut::Unsat(_) => return Ok(RunnerResult { num_tries: i }),
                RunnerOut::Timeout(_) => continue,
                _ => unreachable!(),
            }
        }
        RunnerError::RanOutOfTries(n).no_location()
    }
}

#[derive(Debug, Clone, Copy, Error)]
pub enum RunnersCreationError {
    #[error("no valid solver available")]
    NoSolver,
}

impl From<RunnersCreationError> for BaseError {
    fn from(val: RunnersCreationError) -> Self {
        RunnerError::from(val).into()
    }
}

impl TryFrom<SolverConfig> for Runners {
    type Error = RunnersCreationError;

    fn try_from(value: SolverConfig) -> Result<Self, Self::Error> {
        let timeout = value.timeout;
        let vampire = if !value.enable_solvers.contains(EnabledSolvers::VAMPIRE) {
            None
        } else {
            which::which(&value.locations.vampire).ok()
        };
        let vampire = vampire.map(|location| VampireExec {
            exe_location: location,
            extra_args: vec![VampireArg::TimeLimit(timeout)],
        });

        let z3 = if !value.enable_solvers.contains(EnabledSolvers::Z3) {
            None
        } else {
            which::which(&value.locations.z3).ok()
        };
        let z3 = z3.map(|location| Z3Runner {
            location,
            extra_args: vec![format!("-T:{timeout:}")],
        });

        let cvc5 = None;

        if vampire.is_none() && z3.is_none() && cvc5.is_none() {
            Err(RunnersCreationError::NoSolver)
        } else {
            Ok(Runners { vampire, z3, cvc5 })
        }
    }
}

/// A [RunnerHandler] that allow for multithreaded process spawning and killing
///
/// This way we can kill all other processes once the first one finishes
#[derive(Debug, Clone)]
struct Handler {
    killable: Sender<Arc<SharedChild>>,
    unkillable: Sender<Arc<SharedChild>>,
}

#[derive(Debug, Error)]
pub enum HandlerError {
    #[error(transparent)]
    IoError(#[from] std::io::Error),
    #[error("no more reciever, child killed")]
    NoMoreReciever,
}
impl From<HandlerError> for BaseError {
    fn from(val: HandlerError) -> Self {
        RunnerError::from(val).into()
    }
}

impl RunnerHandler for Handler {
    type Error = HandlerError;

    fn spawn_killable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error> {
        let child = Arc::new(SharedChild::spawn(child)?);
        if self.killable.send(Arc::clone(&child)).is_err() {
            debug!("no more reciever, trying to kill child");
            kill_shared_child(&child)?;
            Err(HandlerError::NoMoreReciever)?
        };
        Ok(child)
    }

    fn spawn_unkillable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error> {
        let child = Arc::new(SharedChild::spawn(child)?);
        if self.unkillable.send(Arc::clone(&child)).is_err() {
            debug!("no more reciever, trying to kill child");
            kill_shared_child(&child)?;
            Err(HandlerError::NoMoreReciever)?
        };
        Ok(child)
    }
}

fn autorun_many<'bump>(
    env: &Environement<'bump>,
    pbl: &mut Problem<'bump>,
    save_to: Option<&Path>,
    runners: &[dyn_traits::RunnerAndDiscoverer<Handler>],
) -> crate::Result<RunnerOut<Infallible, (), (), Infallible>> {
    let to_analyse = thread::scope(|s| {
        let (killable_send, killable_recv) = channel();
        let (unkillable_send, unkillable_recv) = channel();
        let (finished_send, finished_recv) = channel();
        let hr = {
            let handler = Handler {
                killable: killable_send,
                unkillable: unkillable_send,
            };
            runners
                .iter()
                .map(|runner| {
                    let handler = handler.clone();
                    let finished = finished_send.clone();
                    let env = &env;
                    let pbl = &pbl;
                    let handle = s.spawn(move || {
                        finished.send((runner, runner.dyn_run_to_tmp(handler, env, pbl, save_to)))
                    });
                    // HandleAndRunner { handle, runner }
                    handle
                })
                .collect_vec()
        };
        drop(finished_send);

        let mut to_analyse = Vec::new();

        let finished_iter = finished_recv.into_iter();

        for r in finished_iter {
            match r {
                (_, Ok(RunnerOut::Sat(_))) => {
                    trace!("sat, killall");
                    killall(killable_recv, unkillable_recv, hr)?;
                    // bail!("disproved the query");
                    return RunnerError::Disprove.no_location();
                }
                (_, Ok(RunnerOut::Unsat(_))) => {
                    trace!("unsat, killall");
                    killall(killable_recv, unkillable_recv, hr)?;
                    return Ok(None);
                }
                (dyn_traits::RunnerAndDiscoverer::Discoverer(d), Ok(RunnerOut::Timeout(t))) => {
                    trace!("timeout in discoverer");
                    to_analyse.push((d, t))
                }
                (_, Err(e)) => {
                    trace!("error in one of the solver");
                    killall(killable_recv, unkillable_recv, hr)?;
                    return Err(e);
                }
                _ => {
                    trace!("other result, ignoring");
                    continue;
                }
            }
        }
        killall(killable_recv, unkillable_recv, hr)?;
        Ok(Some(to_analyse))
    })?;

    // analysed gathered data
    if let Some(to_analyse) = to_analyse {
        for (discoverer, out) in to_analyse {
            discoverer.dyn_discover(env, pbl, out.as_ref())?
        }
        Ok(RunnerOut::Timeout(()))
    } else {
        Ok(RunnerOut::Unsat(()))
    }
}

fn killall<T>(
    killalble: Receiver<Arc<SharedChild>>,
    unkillalble: Receiver<Arc<SharedChild>>,
    threads: Vec<ScopedJoinHandle<'_, T>>,
) -> crate::Result<()> {
    debug!("killing all");
    chain!(killalble.into_iter(), unkillalble.into_iter())
        .map(|c| kill_shared_child(&c))
        .collect_vec() // make sure we stop them all
        .into_iter()
        .try_for_each(|x: io::Result<()>| x)?;

    threads
        .into_iter()
        .map(|h| h.join())
        // .collect_vec()
        // .into_iter()
        .for_each(|r| match r {
            Ok(_) => (),
            Err(e) => std::panic::resume_unwind(e), // keep panicing
        });

    Ok(())
}

fn kill_shared_child(child: &SharedChild) -> io::Result<()> {
    debug!("killing {}", child.id());
    child.kill()?;
    thread::sleep(Duration::from_millis(5));
    child.wait()?;
    Ok(())
}
