use std::{
    io::BufWriter,
    num::NonZeroU32,
    path::Path,
    process::{Child, Command},
    sync::{
        mpsc::{channel, Sender},
        Arc, Mutex,
    },
    thread,
};

use anyhow::{bail, ensure};
use log::{debug, trace};
use shared_child::SharedChild;
use tempfile::Builder;
use thiserror::Error;
use utils::traits::MyWriteTo;

use crate::{
    environement::environement::Environement,
    problem::{crypto_assumptions::CryptoAssumption, Problem},
    smt::SmtFile,
};

use super::{searcher::InstanceSearcher, z3::Z3Runner, VampireExec};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum RunnerOut<S, U, T, O> {
    Sat(S),
    Unsat(U),
    Timeout(T),
    Other(O),
}

pub type RunnerBase = RunnerOut<(), (), (), ()>;

pub type RunnerOutI<X> = RunnerOut<
    <X as Runner>::SatR,
    <X as Runner>::UnsatR,
    <X as Runner>::TimeoutR,
    <X as Runner>::OtherR,
>;

pub trait RunnerHandler {
    type Error: std::error::Error + Send + Sync + 'static;
    fn spawn_killable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error>;
    fn spawn_unkillable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error>;
}

pub trait Runner {
    type Args<'a>;
    type SatR;
    type UnsatR;
    type TimeoutR;
    type OtherR;

    /// Run `pbl_file` using the parameter defined by `args`
    fn run<'a, R>(
        &self,
        handler: R,
        args: Self::Args<'a>,
        pbl_file: &Path,
    ) -> anyhow::Result<RunnerOutI<Self>>
    where
        R: RunnerHandler + Clone;

    fn run_to_tmp<'a, 'bump, R>(
        &self,
        handler: R,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
        args: Self::Args<'a>,
        save_to: Option<&Path>,
    ) -> anyhow::Result<RunnerOutI<Self>>
    where
        R: RunnerHandler + Clone,
    {
        if let Some(p) = save_to {
            std::fs::create_dir_all(p)?
        }

        let prefix = format!("cryptovampire-{}", Self::get_file_prefix());
        let mut tmp_builder = Builder::new();
        tmp_builder.suffix(Self::get_file_suffix());
        tmp_builder.prefix(&prefix);

        let mut file = tmp_builder.tempfile()?; // gen tmp file

        self.write(env, pbl, &mut BufWriter::new(&mut file))?;
        let r = self.run(handler, args, file.path())?;

        if let Some(p) = save_to {
            debug_assert_ne!("..", Self::get_file_suffix());
            let name = p.join(file.path().file_name().unwrap()); // can't end in ".."
            trace!("copying file to {name:?}");
            std::fs::copy(file.path(), name)?;
        };
        return Ok(r);
    }

    fn write<'bump, W: std::io::Write>(
        &self,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
        file: W,
    ) -> anyhow::Result<()>;

    /// The file extension for the temporary file, defaults to `".smt"`
    fn get_file_suffix() -> &'static str {
        ".smt"
    }

    fn get_file_prefix() -> &'static str;

    fn default_args(&self) -> Self::Args<'_>;
}

#[derive(Debug, Error)]
pub enum DiscovererError {
    #[error("no new instances")]
    NoNewInstances,
    #[error("other error {0}")]
    Other(#[from] anyhow::Error),
}

pub trait Discoverer
where
    Self: Runner + Sized,
    for<'bump> CryptoAssumption<'bump>: InstanceSearcher<'bump, Self>,
{
    fn discover<'bump>(
        &self,
        env: &Environement<'bump>,
        pbl: &mut Problem<'bump>,
        out: &<Self as Runner>::TimeoutR,
    ) -> Result<(), DiscovererError>;
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
                child.kill()?;
                child.wait()?;
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
                child.kill()?;
                child.wait()?;
                Err(HandlerError::NoMoreReciever)?
            }
            _ => (),
        };
        Ok(child)
    }
}

impl RunnerHandler for () {
    type Error = std::io::Error;

    fn spawn_killable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error> {
        Ok(Arc::new(SharedChild::spawn(child)?))
    }

    fn spawn_unkillable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error> {
        Ok(Arc::new(SharedChild::spawn(child)?))
    }
}

pub struct Runners {
    pub vampire: Option<VampireExec>,
    pub z3: Option<Z3Runner>,
}

impl Runners {
    pub fn all_empty(&self) -> bool {
        matches!(&self.vampire, None)
    }

    pub fn autorun<'bump>(
        &self,
        env: &Environement<'bump>,
        pbl: &mut Problem<'bump>,
        ntimes: Option<NonZeroU32>,
        save_to: Option<&Path>,
    ) -> anyhow::Result<String> {
        ensure!(!self.all_empty(), "no solver to run :'(");
        let n: u32 = ntimes.map(NonZeroU32::get).unwrap_or(u32::MAX);

        for i in 0..n {
            debug!("running {i:}/{n:}");
            let (killable_send, killable_recv) = channel();
            let (unkillable_send, unkillable_recv) = channel();

            let res: anyhow::Result<_> = thread::scope(|s| {
                let vjh;
                let z3jh;
                {
                    let handler = Handler {
                        killable: killable_send,
                        unkillable: unkillable_send,
                    };
                    vjh = self.vampire.as_ref().map(|vr| {
                        let handler = handler.clone();
                        s.spawn(|| vr.run_to_tmp(handler, env, pbl, vr.default_args(), save_to))
                    });
                    z3jh = self.z3.as_ref().map(|z3| {
                        let handler = handler.clone();
                        s.spawn(|| z3.run_to_tmp(handler, env, pbl, z3.default_args(), save_to))
                    });
                } // handler dropped here

                let mut res = false;
                for r in unkillable_recv {
                    res = res || r.wait()?.success();
                }

                // TODO: make sure they failled before killing everyone

                for r in killable_recv {
                    r.kill()?;
                    r.wait()?; // avoid zombie
                }
                Ok((
                    vjh.map(|h| h.join().unwrap()),
                    z3jh.map(|h| h.join().unwrap()),
                ))
            });
            let (vout, z3out) = res?;

            let vout = vout.transpose()?;
            let z3out = z3out.transpose()?;

            match z3out {
                Some(RunnerOut::Unsat(_)) => return Ok("z3 found a solution".into()),
                Some(RunnerOut::Sat(_)) => bail!("z3 disproved the problem"),
                _ => (),
            }

            let data = match vout {
                Some(RunnerOut::Unsat(proof)) => return Ok(proof),
                Some(RunnerOut::Timeout(data)) => Some(data),
                Some(RunnerOut::Sat(proof)) => bail!("the query is false:\n{proof}"),
                None => None,
                _ => bail!("unknown error"),
            };
            match (&self.vampire, data) {
                (Some(vr), Some(out)) => vr.discover(env, pbl, &out)?,
                _ => (),
            }
        }
        bail!("ran out of tries (at most {n})")
    }
}
