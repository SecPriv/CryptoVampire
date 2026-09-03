//! `cvc5` [Runner]

use std::path::PathBuf;
use std::process::{Command, Stdio};

use itertools::chain;
use log::debug;
use utils::traits::MyWriteTo;

use super::Runner;
use super::runner::ChildKind;
use crate::environement::environement::{Environement, Flags, SubtermFlags};
use crate::error::{BaseContext, CVContext};
use crate::runner::{RetCodeAndStdout, RunnerOut, exec_cmd};
use crate::smt::SmtFile;
use crate::{FromEnv, SmtDisplay, ensure};
/// The [Runner] for `cvc5`.
///
/// Like `z3`, this is a *dumb* runner: we just dump a standard-compliant SMT
/// file at it and read back `sat`/`unsat`/`unknown`. In particular we never
/// try to extract instances from its output (contrary to `vampire`).
#[derive(Debug, Clone)]
pub struct Cvc5Runner {
    pub location: PathBuf,
    pub extra_args: Vec<String>,
}

impl Runner for Cvc5Runner {
    type Args<'a> = &'a [String];

    type SatR = ();

    type UnsatR = ();

    type TimeoutR = ();

    type OtherR = String;

    fn write<'bump, W: std::io::Write>(
        &self,
        env: &Environement<'bump>,
        pbl: &crate::problem::Problem<'bump>,
        mut file: W,
    ) -> crate::Result<()> {
        use std::io::Write as _;

        // `cvc5` is stricter than `z3` about SMT-LIB compliance: drop *all* the
        // non-standard extensions (`assert-not`, `assert-theory`,
        // `assert-ground` and the vampire subterm relation) or it will refuse
        // the file.
        let mut env = env.clone();
        env.options_mut().flags -= Flags::NON_SMT_STANDARD;
        env.options_mut().subterm_flags -= SubtermFlags::VAMPIRE;
        let env = &env;

        // Tell cvc5 upfront which logic we're in. The examples only use free
        // (uninterpreted) functions, quantifiers, equality and a single
        // datatype (`Name`) so `UFDT` is the right theory. It both silences
        // the "No set-logic command was given before this point" warning and
        // lets cvc5 enable logic-specific heuristics.
        writeln!(file, "(set-logic UFDT)")?;

        SmtFile::with_env(env, pbl.into_general_file(env)) // gen smt
            .as_display(env)
            .write_to_io(&mut file)?;
        Ok(())
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
        debug!("running cvc5 with {cmd:?}");

        let result = exec_cmd(self, handler, &mut cmd)?;

        match result {
            RetCodeAndStdout::Success {
                stdout,
                return_code: 0,
            } => {
                let last_line = stdout.lines().last().with_message(|| "no output")?.trim();
                // cvc5 answers either `unsat`, `sat` or `unknown` on the last
                // line (the latter being e.g. `unknown (TIMEOUT)`). Prefix
                // matching keeps us robust to those suffixed variants.
                if last_line.starts_with("unsat") {
                    Ok(RunnerOut::Unsat(()))
                } else if last_line.starts_with("sat") {
                    Ok(RunnerOut::Sat(()))
                } else if last_line.starts_with("unknown") {
                    Ok(RunnerOut::Timeout(()))
                } else {
                    Ok(RunnerOut::Other(stdout))
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
        "cvc5"
    }

    fn kind(&self) -> super::runner::ChildKind {
        ChildKind::Killable
    }
}
