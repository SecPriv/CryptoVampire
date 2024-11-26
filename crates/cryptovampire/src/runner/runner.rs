use std::{
    io::BufWriter,
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

use log::{info, trace};
use shared_child::SharedChild;
use tempfile::{Builder, NamedTempFile};
use thiserror::Error;

use crate::{
    environement::environement::Environement,
    error::BaseError,
    problem::{crypto_assumptions::CryptoAssumption, Problem},
};

use super::{dyn_traits, searcher::InstanceSearcher, RetCodeAndStdout, RunnerError};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum RunnerOut<S, U, T, O> {
    Sat(S),
    Unsat(U),
    Timeout(T),
    Other(O),
}

pub type RunnerBase = RunnerOut<(), (), (), ()>;
const SAT: RunnerBase = RunnerOut::Sat(());
const UNSAT: RunnerBase = RunnerOut::Unsat(());
const TIMEOUT: RunnerBase = RunnerOut::Timeout(());
const OTHER: RunnerBase = RunnerOut::Other(());

pub type RunnerOutI<X> = RunnerOut<
    <X as Runner>::SatR,
    <X as Runner>::UnsatR,
    <X as Runner>::TimeoutR,
    <X as Runner>::OtherR,
>;

impl<S, U, T, O> RunnerOut<S, U, T, O> {
    /// Returns `true` if the runner out is [`Sat`].
    ///
    /// [`Sat`]: RunnerOut::Sat
    #[must_use]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat(..))
    }

    /// Returns `true` if the runner out is [`Unsat`].
    ///
    /// [`Unsat`]: RunnerOut::Unsat
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat(..))
    }

    /// Returns `true` if the runner out is [`Timeout`].
    ///
    /// [`Timeout`]: RunnerOut::Timeout
    #[must_use]
    pub fn is_timeout(&self) -> bool {
        matches!(self, Self::Timeout(..))
    }

    /// Returns `true` if the runner out is [`Other`].
    ///
    /// [`Other`]: RunnerOut::Other
    #[must_use]
    pub fn is_other(&self) -> bool {
        matches!(self, Self::Other(..))
    }

    pub fn into_dyn(self) -> dyn_traits::RunnerOutDyn
    where
        S: Send + 'static,
        U: Send + 'static,
        T: Send + 'static,
        O: Send + 'static,
    {
        match self {
            RunnerOut::Sat(s) => RunnerOut::Sat(Box::new(s)),
            RunnerOut::Unsat(u) => RunnerOut::Unsat(Box::new(u)),
            RunnerOut::Timeout(t) => RunnerOut::Timeout(Box::new(t)),
            RunnerOut::Other(o) => RunnerOut::Other(Box::new(o)),
        }
    }
}

impl<S, U, T, O> AsRef<RunnerBase> for RunnerOut<S, U, T, O> {
    fn as_ref(&self) -> &RunnerBase {
        match self {
            RunnerOut::Sat(_) => &SAT,
            RunnerOut::Unsat(_) => &UNSAT,
            RunnerOut::Timeout(_) => &TIMEOUT,
            RunnerOut::Other(_) => &OTHER,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChildKind {
    Killable,
    Unkillable,
}
pub trait RunnerHandler {
    type Error: std::error::Error + Send + Sync + 'static + Into<BaseError>;
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
    fn run<R>(
        &self,
        handler: R,
        args: Self::Args<'_>,
        pbl_file: &Path,
    ) -> crate::Result<RunnerOutI<Self>>
    where
        R: RunnerHandler + Clone;

    fn run_to_tmp<'bump, R>(
        &self,
        handler: R,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
        args: Self::Args<'_>,
        save_to: Option<&Path>,
    ) -> crate::Result<RunnerOutI<Self>>
    where
        R: RunnerHandler + Clone,
    {
        trace!("start {}", Self::name());
        let mut file = build_file::<Self>(save_to)?;
        self.write(env, pbl, &mut BufWriter::new(&mut file))?; // write to it
        let file = file; // deactivate mutation
        let path = file.path();
        info!("running {} to {:?}.", Self::name(), path);

        let r = self.run(handler, args, path)?;
        Ok(r)
    }

    fn write<'bump, W: std::io::Write>(
        &self,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
        file: W,
    ) -> crate::Result<()>;

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

    fn kind(&self) -> ChildKind;

    fn unexpected_result(cmd: Command, return_code: i32, stdout: String) -> BaseError {
        RunnerError::UnexpectedResult {
            tool: Self::name(),
            return_code,
            cmd,
            stdout,
        }
        .into()
    }
}

fn build_file<R: Runner + ?Sized>(save_to: Option<&Path>) -> crate::Result<NamedTempFile> {
    let base_prefix = PathBuf::from(format!("cryptovampire-{}", R::get_file_prefix()));

    let prefix = match save_to {
        Some(p) => {
            std::fs::create_dir_all(p)?;
            p.join(base_prefix)
        }
        None => base_prefix,
    };
    let mut tmp_builder = Builder::new();
    tmp_builder
        .suffix(R::get_file_suffix())
        .prefix(&prefix)
        .keep(save_to.is_some());
    let file = tmp_builder.tempfile()?; // gen tmp file
    info!("generated file {}", file.path().to_string_lossy());
    Ok(file)
}

#[derive(Debug, Error)]
pub enum DiscovererError {
    #[error("no new instances")]
    NoNewInstances,
    // #[error("other error {0}")]
    // Other(#[from] crate::Error),
}

impl From<DiscovererError> for BaseError {
    fn from(val: DiscovererError) -> Self {
        RunnerError::from(val).into()
    }
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
    ) -> crate::Result<()>;
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
