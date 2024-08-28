use std::{
    convert::Infallible,
    io,
    num::NonZeroU32,
    path::Path,
    process::Command,
    sync::{
        mpsc::{channel, Receiver, Sender},
        Arc,
    },
    thread::{self, ScopedJoinHandle},
    time::Duration,
};

use anyhow::{bail, ensure};
use itertools::{chain, Itertools};
use log::{debug, trace};
use shared_child::SharedChild;
use thiserror::Error;

use crate::{
    environement::environement::{EnabledSolvers, Environement, SolverConfig},
    problem::Problem,
    runner::RunnerOut,
};

use super::{
    dyn_traits::{self, DynRunner},
    z3::Z3Runner,
    RunnerHandler, VampireArg, VampireExec,
};

#[derive(Debug, Clone)]
pub struct Runners {
    pub vampire: Option<VampireExec>,
    pub z3: Option<Z3Runner>,
    pub cvc5: Option<Infallible>,
}

impl Runners {
    pub fn all_empty(&self) -> bool {
        matches!(&self.vampire, None) && matches!(&self.z3, None) && matches!(&self.cvc5, None)
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
    ) -> anyhow::Result<String> {
        ensure!(!self.all_empty(), "no solver to run :'(");
        let n: u32 = ntimes.map(NonZeroU32::get).unwrap_or(u32::MAX);

        let Runners { vampire, z3, .. } = self;

        let v = vampire.map(|v| dyn_traits::RunnerAndDiscoverer::Discoverer(Box::new(v)));
        let z3 = z3.map(|v| dyn_traits::RunnerAndDiscoverer::Runner(Box::new(v)));
        let runners = [v, z3].into_iter().flatten().collect_vec();

        for i in 0..n {
            debug!("running {i:}/{n:}");

            let res = autorun_many(env, pbl, save_to, &runners)?;

            match res {
                RunnerOut::Unsat(_) => return Ok("proven".into()),
                RunnerOut::Timeout(_) => continue,
                _ => unreachable!(),
            }
        }
        bail!("ran out of tries (at most {n})")
    }
}

#[derive(Debug, Clone, Copy, Error)]
pub enum RunnersCreationError {
    #[error("no valid solver available")]
    NoSolver,
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
            location,
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

impl RunnerHandler for Handler {
    type Error = HandlerError;

    fn spawn_killable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error> {
        let child = Arc::new(SharedChild::spawn(child)?);
        match self.killable.send(Arc::clone(&child)) {
            Err(_) => {
                debug!("no more reciever, trying to kill child");
                kill_shared_child(&child)?;
                Err(HandlerError::NoMoreReciever)?
            }
            _ => (),
        };
        Ok(child)
    }

    fn spawn_unkillable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error> {
        let child = Arc::new(SharedChild::spawn(child)?);
        match self.unkillable.send(Arc::clone(&child)) {
            Err(_) => {
                debug!("no more reciever, trying to kill child");
                kill_shared_child(&child)?;
                Err(HandlerError::NoMoreReciever)?
            }
            _ => (),
        };
        Ok(child)
    }
}

fn autorun_many<'bump>(
    env: &Environement<'bump>,
    pbl: &mut Problem<'bump>,
    save_to: Option<&Path>,
    runners: &[dyn_traits::RunnerAndDiscoverer<Handler>],
) -> anyhow::Result<RunnerOut<Infallible, (), (), Infallible>> {
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

        let mut finished_iter = finished_recv.into_iter();

        while let Some(r) = finished_iter.next() {
            match r {
                (_, Ok(RunnerOut::Sat(_))) => {
                    trace!("sat, killall");
                    killall(killable_recv, unkillable_recv, hr)?;
                    bail!("disproved the query");
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
                (_, e @ Err(_)) => {
                    trace!("error in one of the solver");
                    killall(killable_recv, unkillable_recv, hr)?;
                    e?;
                    unreachable!();
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

fn killall<'a, 's, T>(
    killalble: Receiver<Arc<SharedChild>>,
    unkillalble: Receiver<Arc<SharedChild>>,
    threads: Vec<ScopedJoinHandle<'s, T>>,
) -> anyhow::Result<()> {
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
