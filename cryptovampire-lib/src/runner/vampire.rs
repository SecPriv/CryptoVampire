use anyhow::{bail, ensure, Context};
use itertools::Itertools;
use log::debug;
use std::{
    path::{Path, PathBuf},
    process::{Command, Stdio},
    usize,
};
use utils::traits::MyWriteTo;

use crate::{
    environement::environement::{Environement, Flags},
    problem::Problem,
    runner::{
        exec_cmd,
        runner::{ChildKind, RunnerOut},
        searcher::InstanceSearcher,
    },
    smt::SmtFile,
};

use super::{
    runner::{Discoverer, DiscovererError, Runner, RunnerOutI},
    RunnerHandler,
};

#[derive(Debug, Clone)]
pub struct VampireExec {
    pub location: PathBuf,
    pub extra_args: Vec<VampireArg>,
}
macro_rules! option {
      ($($variant:ident($name:literal, $content:ty)),*,) => {
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

const SUCCESS_RC: i32 = 0;
const TIMEOUT_RC: i32 = 1;

impl Runner for VampireExec {
    type Args<'a> = &'a [VampireArg];

    type SatR = String;

    type UnsatR = String;

    type TimeoutR = String;

    type OtherR = String;

    fn run<'a, R: RunnerHandler + Clone>(
        &self,
        handler: R,
        args: Self::Args<'a>,
        pbl_file: &Path,
    ) -> anyhow::Result<RunnerOutI<Self>> {
        ensure!(
            // check the file exists
            pbl_file.is_file(),
            "{} is not a file",
            pbl_file.to_str().unwrap_or("[not unicode]")
        );
        let mut cmd = Command::new(&self.location);
        for arg in self.extra_args.iter().chain(args.into_iter()) {
            // encode the arguments
            let [a, b] = arg.to_args();
            cmd.arg(a.as_ref()).arg(b.as_ref());
        }
        cmd.arg(pbl_file) // encode the file
            .stdout(Stdio::piped());
        debug!("running vampire with {cmd:?}");

        let result = exec_cmd(self, handler, &mut cmd)?;

        match result.return_code {
            SUCCESS_RC => Ok(RunnerOut::Unsat(result.stdout)),
            TIMEOUT_RC => Ok(RunnerOut::Timeout(result.stdout)),
            _ => bail!("Unknow Error while running vampire:\n\tcmd:{cmd:?}\n\treturn code: {:}\n\tstdout:\n{}", result.return_code, result.stdout),
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
    ) -> anyhow::Result<()> {
        let mut env = env.clone();
        env.options_mut().flags |= Flags::ASSERT_NOT | Flags::ASSERT_THEORY;
        let env = &env;

        SmtFile::from_general_file(env, pbl.into_general_file(env)) // gen smt
            .as_diplay(env)
            .write_to_io(&mut file)
            .with_context(|| "couldn't write") // write to tmp file
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
    ) -> Result<(), DiscovererError> {
        // find new instances
        let new_instances = pbl
            .crypto_assertions()
            .iter()
            .map(|ca| ca.search_instances(new_instances_str, env))
            .flatten()
            .collect_vec();
        if new_instances.is_empty() {
            // no new instances, no need to try again
            return Err(DiscovererError::NoNewInstances);
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
            return Err(DiscovererError::NoNewInstances);
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
