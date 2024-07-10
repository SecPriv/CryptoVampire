use std::{
    io::Read,
    path::PathBuf,
    process::{Command, Stdio},
};

use anyhow::{bail, ensure, Context};
use itertools::chain;
use log::debug;
use utils::traits::MyWriteTo;

use crate::{environement::environement::Flags, runner::RunnerOut, smt::SmtFile};

use super::Runner;

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
        let child = handler.spawn_killable_child(&mut cmd)?;

        // wait for the proccess
        let exit_status = child.wait()?;

        // read the output from the process
        let stdout = {
            let mut out = String::default();
            child
                .take_stdout()
                .map(|mut s| s.read_to_string(&mut out))
                .transpose()
                .with_context(|| format!("z3 ({:?})'s output isn't in utf-8", &self.location))?;
            out
        };
        if exit_status.success() {
            let last_line = stdout.lines().last().with_context(|| "no output")?.trim();
            match last_line {
                "unsat" => return Ok(RunnerOut::Unsat(())),
                "sat" => return Ok(RunnerOut::Sat(())),
                _ => return Ok(RunnerOut::Other(stdout)),
            }
        }

        bail!("Error while running z3:\n\tcmd:{cmd:?}\n\tstdout:\n{stdout}")
    }
    
    fn name() -> &'static str {
        "z3"
    }
}
