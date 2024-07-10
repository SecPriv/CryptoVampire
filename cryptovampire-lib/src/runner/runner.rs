use core::time;
use std::{
    convert::Infallible,
    io::BufWriter,
    num::NonZeroU32,
    path::Path,
    process::Command,
    sync::{
        mpsc::{channel, Sender},
        Arc,
    },
    thread,
};

use anyhow::{bail, ensure};
use log::{debug, info, trace};
use shared_child::SharedChild;
use tempfile::Builder;
use thiserror::Error;

use crate::{
    environement::environement::{EnabledSolvers, Environement, SolverConfig},
    problem::{crypto_assumptions::CryptoAssumption, Problem},
};

use super::{searcher::InstanceSearcher, z3::Z3Runner, VampireArg, VampireExec};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChildKind {
    Killable,
    Unkillable,
}
pub trait RunnerHandler {
    type Error: std::error::Error + Send + Sync + 'static;
    fn spawn_killable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error>;
    fn spawn_unkillable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error>;

    fn spawn_child(
        self,
        child: &mut Command,
        kind: ChildKind,
    ) -> Result<Arc<SharedChild>, Self::Error>
    where
        Self: Sized,
    {
        match kind {
            ChildKind::Killable => self.spawn_killable_child(child),
            ChildKind::Unkillable => self.spawn_unkillable_child(child),
        }
    }
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
        trace!("start {}", Self::name());
        if let Some(p) = save_to {
            std::fs::create_dir_all(p)?
        }

        let prefix = format!("cryptovampire-{}", Self::get_file_prefix());
        let mut tmp_builder = Builder::new();
        tmp_builder.suffix(Self::get_file_suffix());
        tmp_builder.prefix(&prefix);

        let mut file = tmp_builder.tempfile()?; // gen tmp file

        self.write(env, pbl, &mut BufWriter::new(&mut file))?; // write to it

        // save it if relevant
        if let Some(p) = save_to {
            debug_assert_ne!("..", Self::get_file_suffix());
            let name = p.join(file.path().file_name().unwrap()); // can't end in ".."
            info!("copying file to {name:?}");
            std::fs::copy(file.path(), name)?;
        };

        let r = self.run(handler, args, file.path())?;
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

    fn get_file_prefix() -> &'static str {
        Self::name()
    }

    fn default_args(&self) -> Self::Args<'_>;

    /// A name for debug purposes
    fn name() -> &'static str;
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

impl RunnerHandler for () {
    type Error = std::io::Error;

    fn spawn_killable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error> {
        Ok(Arc::new(SharedChild::spawn(child)?))
    }

    fn spawn_unkillable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error> {
        Ok(Arc::new(SharedChild::spawn(child)?))
    }
}
