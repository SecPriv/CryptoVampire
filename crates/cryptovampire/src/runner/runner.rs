//!
//!
//!
//!
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
    ensure,
    environement::environement::Environement,
    error::BaseError,
    problem::{crypto_assumptions::CryptoAssumption, Problem},
};

use super::{dyn_traits, searcher::InstanceSearcher,  RunnerError};

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
/// A trait to abstract away how to spawn processes from the [Runner]
///
/// This way we can change how processes are dealt with. This prevent the
/// synchronisation procedures to leak into the implementation of the [Runner]s.
/// See [super::Handler] for such an example
pub trait RunnerHandler {
    type Error: std::error::Error + Send + Sync + 'static + Into<BaseError>;
    fn spawn_killable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error>;
    /// Initially designed for processes that we'd like to keep running even when
    /// it's likely that they will fail.
    fn spawn_unkillable_child(self, child: &mut Command) -> Result<Arc<SharedChild>, Self::Error>;

    /// Gather [spawn_killable_child] and [spawn_unkillable_child] in one
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

/// Something that can launch a specific solver.
///
/// The associated types let us specify which kind of parameters and outputs we
/// can expect from the [Runner]. This way we could in the future easily parse
/// the output of a solver, or have more type safety in its paramenters.
///
/// We later define an object safe restricted version of this trait [dyn_traits::DynRunner]
/// to allow us to use dynamic dispach. See [dyn_traits] for more information
pub trait Runner {
    /// The type of arguments/paramenters
    type Args<'a>;
    /// Return type in case we get a model
    type SatR;
    /// Return type in case of `unsat`
    type UnsatR;
    /// Return type in case of timeout
    type TimeoutR;
    /// Return type otherwise
    type OtherR;

    /// Run `pbl_file` using the parameter defined by `args`, where the content of
    /// `pbl_file` was generated by [write].
    ///
    /// `handler` gives us access to the API to spawn processes.
    fn run<R>(
        &self,
        handler: R,
        args: Self::Args<'_>,
        pbl_file: &Path,
    ) -> crate::Result<RunnerOutI<Self>>
    where
        R: RunnerHandler + Clone;

    /// Write `pbl` into `file` with the configuration correponding to the solver
    ///
    /// # Example
    /// For `vampire`, we can make use of some `smt-lib` extensions like `assert-theory` and (more importantly)
    /// tell what the goal is using `assert-not`.
    ///
    /// On the other hand `cvc5` would reject such a non standard `smt` file.
    fn write<'bump, W: std::io::Write>(
        &self,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
        file: W,
    ) -> crate::Result<()>;

    /// helper based on [run] write a tmp file and run it
    ///
    /// This sort of serves as glue between [run] and [write] to unify the behaviour of the solvers.
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

    /// The file extension for the temporary file, defaults to `".smt"`
    fn get_file_suffix() -> &'static str {
        ".smt"
    }

    fn get_file_prefix() -> &'static str {
        Self::name()
    }

    /// The default arguments
    fn default_args(&self) -> Self::Args<'_>;

    /// The name of the [Runner]
    ///
    /// For debuging and to name files
    fn name() -> &'static str;

    /// See [RunnerHandler]
    fn kind(&self) -> ChildKind;

    /// Shortcut to crash
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

/// create a file in the `save_to` directory, or a temporary file
fn build_file<R: Runner + ?Sized>(save_to: Option<&Path>) -> crate::Result<NamedTempFile> {
    let base_prefix = PathBuf::from(format!("cryptovampire-{}", R::get_file_prefix()));

    let prefix = match save_to {
        Some(p) => {
            ensure!(
                (),
                !p.is_file(),
                "{p:?} is a file. It should be a directory."
            )?;
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
    /// If there are no new instance, there is no need to continue,
    /// hence the error
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

/// A [Runner] that can also discover new instances
///
/// [CryptoAssumption] must be "ready" to make new instances by implementing the right [InstanceSearcher]
///
/// [InstanceSearcher] lets us find which formula may contain instances, then it's up to [Discoverer::discover]
/// to find thoses instances (using [extend_extra_instances])
///
/// [extend_extra_instances]: cryptovampire::problem::problem::Problem::extend_extra_instances
pub trait Discoverer
where
    Self: Runner + Sized,
    for<'bump> CryptoAssumption<'bump>: InstanceSearcher<'bump, Self>,
{
    /// discover new instances, the result is returned by mutating `pbl`
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
