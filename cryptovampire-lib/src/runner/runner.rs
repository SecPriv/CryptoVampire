use std::{future::Future, io::BufWriter, path::Path};

use anyhow::ensure;
use log::trace;
use tempfile::Builder;
use utils::traits::MyWriteTo;

use crate::{environement::environement::Environement, problem::{crypto_assumptions::CryptoAssumption, Problem}, smt::SmtFile};

use super::searcher::InstanceSearcher;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum RunnerOut<S, U, T, O> {
    Sat(S),
    Unsat(U),
    Timeout(T),
    Other(O),
}

pub type RunnerBase = RunnerOut<(), (), (), ()>;

pub type RunnerOutI<X: Runner> = RunnerOut<X::SatR, X::UnsatR, X::TimeoutR, X::OtherR>;

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

pub trait AutoDiscoverer where Self: Runner + Sized,  for<'bump> CryptoAssumption<'bump>:InstanceSearcher<'bump, Self> {
    fn run_and_discover()
}
