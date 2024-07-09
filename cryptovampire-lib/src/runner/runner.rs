use std::{io::BufWriter, num::NonZeroU32, path::Path};

use anyhow::{bail, ensure};
use log::{debug, trace};
use tempfile::Builder;
use thiserror::Error;
use utils::traits::MyWriteTo;

use crate::{
    environement::environement::Environement,
    problem::{crypto_assumptions::CryptoAssumption, Problem},
    runner::DEFAULT_VAMPIRE_ARGS,
    smt::SmtFile,
};

use super::{searcher::InstanceSearcher, VampireExec};

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

pub trait Runner {
    type Args<'a>;
    type SatR;
    type UnsatR;
    type TimeoutR;
    type OtherR;

    /// Run `pbl_file` using the parameter defined by `args`
    fn run<'a>(&self, args: Self::Args<'a>, pbl_file: &Path) -> anyhow::Result<RunnerOutI<Self>>;

    fn run_to_tmp<'a, 'bump>(
        &self,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
        args: Self::Args<'a>,
        save_to: Option<&Path>,
    ) -> anyhow::Result<RunnerOutI<Self>> {
        if let Some(p) = save_to {
            std::fs::create_dir_all(p)?
        }

        let prefix = format!("cryptovampire-{}", Self::get_file_prefix());
        let mut tmp_builder = Builder::new();
        tmp_builder.suffix(Self::get_file_suffix());
        tmp_builder.prefix(&prefix);

        let mut file = tmp_builder.tempfile()?; // gen tmp file

        SmtFile::from_general_file(env, pbl.into_general_file(&env)) // gen smt
            .as_diplay(env)
            .write_to_io(&mut BufWriter::new(&mut file))?; // write to tmp file
        let r = self.run(args, file.path())?;

        if let Some(p) = save_to {
            debug_assert_ne!("..", Self::get_file_suffix());
            let name = p.join(file.path().file_name().unwrap()); // can't end in ".."
            trace!("copying file to {name:?}");
            std::fs::copy(file.path(), name)?;
        };
        return Ok(r);
    }

    /// The file extension for the temporary file, defaults to `".smt"`
    fn get_file_suffix() -> &'static str {
        ".smt"
    }

    fn get_file_prefix() -> &'static str;
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

pub struct Runners {
    pub vampire: Option<VampireExec>,
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
            let vout = self
                .vampire
                .as_ref()
                .map(|vr| vr.run_to_tmp(env, pbl, &DEFAULT_VAMPIRE_ARGS, save_to))
                .transpose()?;

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
