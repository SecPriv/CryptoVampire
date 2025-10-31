//! `z3` [Runner]
use std::path::PathBuf;
use std::process::{Command, Stdio};

use itertools::chain;
use log::debug;
use utils::traits::MyWriteTo;

use super::Runner;
use super::runner::ChildKind;
use crate::environement::environement::Flags;
use crate::error::{BaseContext, CVContext};
use crate::runner::{RetCodeAndStdout, RunnerOut, exec_cmd};
use crate::smt::SmtFile;
use crate::{FromEnv, SmtDisplay, ensure};

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
    ) -> crate::Result<()> {
        let mut env = env.clone();
        env.options_mut().flags -= Flags::NON_SMT_STANDARD;
        let env = &env;

        SmtFile::with_env(env, pbl.into_general_file(env)) // gen smt
            .as_display(env)
            .write_to_io(&mut file)?;
        Ok(())
        // .with_context(|| "couldn't write") // write to tmp file
    }

    fn default_args(&self) -> Self::Args<'_> {
        &[]
    }

    fn run<R>(
        &self,
        handler: R,
        args: Self::Args<'_>,
        pbl_file: &std::path::Path,
    ) -> crate::Result<super::RunnerOutI<Self>>
    where
        R: super::RunnerHandler + Clone,
    {
        ensure!(
            (),
            // check the file exists
            pbl_file.is_file(),
            "{} is not a file",
            pbl_file.to_string_lossy()
        )?;
        let mut cmd = Command::new(&self.location);
        cmd.args(chain!(&self.extra_args, args))
            .arg(pbl_file) // encode the file
            .stdout(Stdio::piped());
        debug!("running z3 with {cmd:?}");

        let result = exec_cmd(self, handler, &mut cmd)?;

        match result {
            RetCodeAndStdout::Success {
                stdout,
                return_code: 0,
            } => {
                let last_line = stdout.lines().last().with_message(|| "no output")?.trim();
                match last_line {
                    "unsat" => Ok(RunnerOut::Unsat(())),
                    "sat" => Ok(RunnerOut::Sat(())),
                    "timeout" => Ok(RunnerOut::Timeout(())),
                    _ => Ok(RunnerOut::Other(stdout)),
                }
            }
            RetCodeAndStdout::Killed { stdout } => Ok(RunnerOut::Other(stdout)),
            RetCodeAndStdout::Success {
                stdout,
                return_code,
            } => Self::unexpected_result(cmd, return_code, stdout).no_location(),
        }
    }

    fn name() -> &'static str {
        "z3"
    }

    fn kind(&self) -> super::runner::ChildKind {
        ChildKind::Killable
    }
}
