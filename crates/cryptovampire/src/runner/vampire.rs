//! The [Runner] for `vampire` and associated surroundings
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use itertools::Itertools;
use log::debug;
use utils::traits::MyWriteTo;

use super::RunnerHandler;
use super::runner::{Discoverer, DiscovererError, Runner, RunnerOutI};
use crate::environement::environement::{Environement, Flags};
use crate::error::CVContext;
use crate::problem::Problem;
use crate::runner::runner::{ChildKind, RunnerOut};
use crate::runner::searcher::InstanceSearcher;
use crate::runner::{RetCodeAndStdout, exec_cmd};
use crate::smt::SmtFile;
use crate::{FromEnv, SmtDisplay, ensure};

/// The [Runner] itself
#[derive(Debug, Clone)]
pub struct VampireExec {
    pub exe_location: PathBuf,
    pub extra_args: Vec<VampireArg>,
}

macro_rules! option {
      ($($variant:ident($name:literal, $content:ty)),*,) => {
          #[doc = "arguments to [VampireExec] in type-safeish mode"]
          #[derive(Debug, Clone, PartialEq, PartialOrd)]
          pub enum VampireArg {
            $($variant($content)),*
          }

          impl ToArgs<2> for VampireArg {
            fn to_args(&self) -> [Box<str>;2] {
              match self {
                $(Self::$variant(x) => {let [y] = x.to_args(); [format!("--{:}", $name).into(), y]})*
              }
            }
          }
      };
    }

option!(
    Cores("cores", u64),
    MemoryLimit("memory_limit", u64),
    Mode("mode", vampire_suboptions::Mode),
    Slowness("slowness", u64),
    TimeLimit("time_limit", f64),
    InputSyntax("input_syntax", vampire_suboptions::InputSyntax),
    NewCnf("newcnf", bool),
    SaturationAlgorithm(
        "saturation_algorithm",
        vampire_suboptions::SaturationAlgorithm
    ),
    Avatar("avatar", bool),
    SatSolver("sat_solver", vampire_suboptions::SatSolver),
    ShowNew("show_new", bool),
    InlineLet("inline_let", bool),
);

pub mod vampire_suboptions {
    use crate::runner::vampire::ToArgs;
    macro_rules! suboption {
      ($name:ident, $(($variant:ident, $content:literal)),*,) => {
          #[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd, Hash, Copy)]
          pub enum $name {
            $($variant),*
          }

          impl ToArgs<1> for $name {
            fn to_args(&self) -> [Box<str>;1] {
              match self {
                $(Self::$variant => [$content.into()]),*
              }
            }
          }
      };
  }

    suboption!(Mode, (Portfolio, "portfolio"),);
    suboption!(
        InputSyntax,
        (SmtLib2, "smtlib2"),
        (Tptp, "tptp"),
        (Auto, "auto"),
    );
    suboption!(
        SaturationAlgorithm,
        (Discount, "discount"),
        (Otter, "otter"),
        (LimitedResources, "lrs"),
        (FiniteModel, "fmb"),
        (Z3, "z3"),
    );
    suboption!(SatSolver, (Minisat, "minisat"), (Z3, "z3"),);
}

/// Turn something into an array of [str] for the [Command] object
trait ToArgs<const N: usize> {
    fn to_args(&self) -> [Box<str>; N];
}

impl ToArgs<1> for u64 {
    fn to_args(&self) -> [Box<str>; 1] {
        [self.to_string().into()]
    }
}

impl ToArgs<1> for f64 {
    fn to_args(&self) -> [Box<str>; 1] {
        [self.to_string().into()]
    }
}

impl ToArgs<1> for bool {
    fn to_args(&self) -> [Box<str>; 1] {
        [if *self { "on" } else { "off" }.into()]
    }
}

/// Success return code
const SUCCESS_RC: i32 = 0;
/// Timeout return code
const TIMEOUT_RC: i32 = 1;

impl Runner for VampireExec {
    type Args<'a> = &'a [VampireArg];

    type SatR = String;

    type UnsatR = String;

    type TimeoutR = String;

    type OtherR = String;

    fn run<R: RunnerHandler + Clone>(
        &self,
        handler: R,
        args: Self::Args<'_>,
        pbl_file: &Path,
    ) -> crate::Result<RunnerOutI<Self>> {
        ensure!(
            (),
            // check the file exists
            pbl_file.is_file(),
            "{} is not a file",
            pbl_file.to_string_lossy()
        )?;
        let mut cmd = Command::new(&self.exe_location);
        for arg in self.extra_args.iter().chain(args.iter()) {
            // encode the arguments
            let [a, b] = arg.to_args();
            cmd.arg(a.as_ref()).arg(b.as_ref());
        }
        cmd.arg(pbl_file) // encode the file
            .stdout(Stdio::piped());
        debug!("running vampire with {cmd:?}");

        let result = exec_cmd(self, handler, &mut cmd)?;

        match result {
            RetCodeAndStdout::Success {
                stdout,
                return_code,
            } => match return_code {
                SUCCESS_RC => Ok(RunnerOut::Unsat(stdout)),
                TIMEOUT_RC => Ok(RunnerOut::Timeout(stdout)),
                _ => Self::unexpected_result(cmd, return_code, stdout).no_location(),
            },
            RetCodeAndStdout::Killed { stdout } => Ok(RunnerOut::Other(stdout)),
        }
    }

    fn default_args(&self) -> Self::Args<'_> {
        &DEFAULT_VAMPIRE_ARGS
    }

    fn write<'bump, W: std::io::Write>(
        &self,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
        mut file: W,
    ) -> crate::Result<()> {
        let mut env = env.clone();
        env.options_mut().flags |= Flags::ASSERT_NOT | Flags::ASSERT_THEORY;
        let env = &env;

        SmtFile::with_env(env, pbl.into_general_file(env)) // gen smt
            .as_display(env)
            .write_to_io(&mut file)
            .map_err(|e| e.into())
        // .with_context(|| "couldn't write") // write to tmp file
    }

    fn name() -> &'static str {
        "vampire"
    }

    fn kind(&self) -> ChildKind {
        ChildKind::Unkillable
    }
}

impl Discoverer for VampireExec {
    fn discover<'bump>(
        &self,
        env: &Environement<'bump>,
        pbl: &mut Problem<'bump>,
        new_instances_str: &<Self as Runner>::TimeoutR,
    ) -> crate::Result<()> {
        // find new instances
        let new_instances = pbl
            .crypto_assertions()
            .iter()
            .flat_map(|ca| ca.search_instances(new_instances_str, env))
            .collect_vec();
        if new_instances.is_empty() {
            // no new instances, no need to try again
            return DiscovererError::NoNewInstances.no_location();
        }

        let max_var_no_instances = pbl.max_var_no_extras();
        if cfg!(debug_assertions) {
            let str = new_instances.iter().map(|t| format!("{:}", t)).join(", ");
            debug!("instances found ({:?}):\n\t[{:}]", new_instances.len(), str)
        }
        let n_new_instances = pbl.extend_extra_instances(
            new_instances
                .into_iter()
                .map(|t| t.translate_vars(max_var_no_instances).into()),
        );

        if n_new_instances == 0 {
            // if all the instances were found before, we bail
            return DiscovererError::NoNewInstances.no_location();
        }
        Ok(())
    }
}

pub const DEFAULT_VAMPIRE_ARGS: [VampireArg; 5] = [
    VampireArg::InputSyntax(vampire_suboptions::InputSyntax::SmtLib2),
    VampireArg::ShowNew(true),
    VampireArg::Avatar(false),
    VampireArg::InlineLet(true),
    VampireArg::NewCnf(true),
];
