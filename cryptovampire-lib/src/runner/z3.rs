use std::{
    io::Read,
    path::PathBuf,
    process::{Command, Stdio},
};

use anyhow::{bail, ensure, Context};
use itertools::chain;
use log::debug;
use utils::traits::MyWriteTo;

use crate::{
    environement::environement::Flags,
    runner::{exec_cmd, RunnerOut},
    smt::SmtFile,
};

use super::{runner::ChildKind, Runner};

#[derive(Debug, Clone)]
pub struct Z3Runner {
    pub location: PathBuf,
    pub extra_args: Vec<String>,
}

impl Runner for Z3Runner {
    type Args<'a> = &'a [String];

    type SatR = ();

    type UnsatR = ();

    type TimeoutR = ();

    type OtherR = String;

    fn write<'bump, W: std::io::Write>(
        &self,
        env: &crate::environement::environement::Environement<'bump>,
        pbl: &crate::problem::Problem<'bump>,
        mut file: W,
    ) -> anyhow::Result<()> {
        let mut env = env.clone();
        env.options_mut().flags -= Flags::NON_SMT_STANDARD;
        let env = &env;

        SmtFile::from_general_file(env, pbl.into_general_file(env)) // gen smt
            .as_diplay(env)
            .write_to_io(&mut file)
            .with_context(|| "couldn't write") // write to tmp file
    }

    fn default_args(&self) -> Self::Args<'_> {
        &[]
    }

    fn run<'a, R>(
        &self,
        handler: R,
        args: Self::Args<'a>,
        pbl_file: &std::path::Path,
    ) -> anyhow::Result<super::RunnerOutI<Self>>
    where
        R: super::RunnerHandler + Clone,
    {
        ensure!(
            // check the file exists
            pbl_file.is_file(),
            "{} is not a file",
            pbl_file.to_str().unwrap_or("[not unicode]")
        );
        let mut cmd = Command::new(&self.location);
        cmd.args(chain!(&self.extra_args, args))
            .arg(pbl_file) // encode the file
            .stdout(Stdio::piped());
        debug!("running z3 with {cmd:?}");

        let result = exec_cmd(self, handler, &mut cmd)?;

        if result.return_code == 0 {
            let last_line = result
                .stdout
                .lines()
                .last()
                .with_context(|| "no output")?
                .trim();
            match last_line {
                "unsat" => return Ok(RunnerOut::Unsat(())),
                "sat" => return Ok(RunnerOut::Sat(())),
                _ => return Ok(RunnerOut::Other(result.stdout)),
            }
        }

        bail!("Error while running z3:\n\tcmd:{cmd:?}\n\t{result:?}")
    }

    fn name() -> &'static str {
        "z3"
    }

    fn kind(&self) -> super::runner::ChildKind {
        ChildKind::Killable
    }
}
