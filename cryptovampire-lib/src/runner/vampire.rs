use anyhow::{bail, ensure, Context};
use itertools::Itertools;
use log::{debug, trace};
use std::{
    io::BufWriter,
    num::NonZeroU32,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    usize,
};
use tempfile::Builder;
use thiserror::Error;
use utils::{implvec, traits::MyWriteTo};

use crate::{
    environement::environement::Environement,
    problem::Problem,
    runner::{runner::RunnerOut, searcher::InstanceSearcher},
    smt::{SmtFile, SMT_FILE_EXTENSION},
};

use super::runner::{Discoverer, DiscovererError, Runner, RunnerOutI};

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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum VampireOutput {
    Unsat(String),
    TimeOut(String),
}

#[derive(Debug, Error)]
pub enum VampireError {
    #[error(
        "\
vampire failed in an unsupported way:
${cmd}
 ==> {return_code}
------------out------------
{stdout}"
    )]
    UnknownError {
        stdout: String,
        // stdin: String,
        cmd: String,
        return_code: i32,
    },
}

const SUCCESS_RC: i32 = 0;
const TIMEOUT_RC: i32 = 1;

impl Runner for VampireExec {
    type Args<'a> = &'a [VampireArg];

    type SatR = String;

    type UnsatR = String;

    type TimeoutR = String;

    type OtherR = String;

    fn run<'a>(&self, args: Self::Args<'a>, pbl_file: &Path) -> anyhow::Result<RunnerOutI<Self>> {
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
        cmd.arg(pbl_file); // encode the file
        debug!("running vampire with {cmd:?}");

        let child = cmd
            // .stdin(Stdio::piped()) // We want to write to stdin
            .stdout(Stdio::piped()) // Capture the stdout
            .spawn()
            .with_context(|| format!("Failed to start vampire ({:?})", &self.location))?;

        // read the output from the process
        let output = child
            .wait_with_output()
            .with_context(|| format!("Failed to read vampire ({:?})'s stdout", &self.location))?;
        let stdout = String::from_utf8(output.stdout)
            .with_context(|| format!("vampire ({:?})'s output isn't in utf-8", &self.location))?;
        let return_code = output
            .status
            .code()
            .with_context(|| "terminated by signal")?;
        match return_code {
            SUCCESS_RC => Ok(RunnerOut::Unsat(stdout)),
            TIMEOUT_RC => Ok(RunnerOut::Timeout(stdout)),
            _ => Err(VampireError::UnknownError {
                cmd: format!("{:?}", cmd),
                stdout,
                return_code,
            })?,
        }
    }

    fn get_file_prefix() -> &'static str {
        "vampire"
    }
}

// impl VampireExec {
//     /// calls `vampire` on `pbl_file` with the extra arguements `args` added to [DEFAULT_VAMPIRE_ARGS]
//     ///
//     /// ## Error
//     /// - if io error (e.g., can't find `vampire`, can't run it, file doesn't exists)
//     /// - `vampire` ends with something that isn't supported by [VampireOutput] (e.g., Saturation, parsing error, etc...)
//     pub fn run<'a>(
//         &'a self,
//         args: implvec!(&'a VampireArg),
//         pbl_file: &Path,
//     ) -> anyhow::Result<VampireOutput> {
//         ensure!(
//             // check the file exists
//             pbl_file.is_file(),
//             "{} is not a file",
//             pbl_file.to_str().unwrap_or("[not unicode]")
//         );
//         let mut cmd = Command::new(&self.location);
//         for arg in self.extra_args.iter().chain(args.into_iter()) {
//             // encode the arguments
//             let [a, b] = arg.to_args();
//             cmd.arg(a.as_ref()).arg(b.as_ref());
//         }
//         cmd.arg(pbl_file); // encode the file
//         debug!("running vampire with {cmd:?}");

//         let child = cmd
//             // .stdin(Stdio::piped()) // We want to write to stdin
//             .stdout(Stdio::piped()) // Capture the stdout
//             .spawn()
//             .with_context(|| format!("Failed to start vampire ({:?})", &self.location))?;

//         // read the output from the process
//         let output = child
//             .wait_with_output()
//             .with_context(|| format!("Failed to read vampire ({:?})'s stdout", &self.location))?;
//         let stdout = String::from_utf8(output.stdout)
//             .with_context(|| format!("vampire ({:?})'s output isn't in utf-8", &self.location))?;
//         let return_code = output
//             .status
//             .code()
//             .with_context(|| "terminated by signal")?;
//         match return_code {
//             SUCCESS_RC => Ok(VampireOutput::Unsat(stdout)),
//             TIMEOUT_RC => Ok(VampireOutput::TimeOut(stdout)),
//             _ => Err(VampireError::UnknownError {
//                 cmd: format!("{:?}", cmd),
//                 stdout,
//                 return_code,
//             })?,
//         }
//     }

//     /// run vampire on the [Problem] `pbl`. It will run vampire `ntimes` times
//     /// and modify `pbl` each time
//     ///
//     /// It uses [tempfile]s to communicate with vampire. Set `save_to` to
//     /// something else than [None] to copy all those tmp file to that location
//     ///
//     /// ## Error
//     /// - if the io fails
//     /// - it runs out of tries
//     /// - if they are no new instances (nothing generated by `vampire` or they
//     /// were all already known)
//     pub fn auto_run_vampire<'bump>(
//         &self,
//         env: &Environement<'bump>,
//         pbl: &mut Problem<'bump>,
//         ntimes: Option<NonZeroU32>,
//         save_to: Option<&Path>,
//     ) -> anyhow::Result<Vec<VampireOutput>> {
//         if let Some(p) = save_to {
//             // make sure the directory exists
//             ensure!(
//                 !p.is_file(),
//                 "{} is a file",
//                 p.to_str().unwrap_or("[non unicode]")
//             );
//             std::fs::create_dir_all(p)?
//         }
//         let n: u32 = ntimes.map(NonZeroU32::get).unwrap_or(u32::MAX);
//         let mut ret = if let Some(n) = ntimes {
//             Vec::with_capacity(n.get() as usize)
//         } else {
//             vec![]
//         };
//         let mut tmp_builder = Builder::new();
//         tmp_builder.suffix(SMT_FILE_EXTENSION);

//         for i in 0..n {
//             debug!("running vampire {i:}/{n:}");
//             let mut file = tmp_builder.tempfile()?; // gen tmp file
//             SmtFile::from_general_file(env, pbl.into_general_file(&env)) // gen smt
//                 .as_diplay(env)
//                 .write_to_io(&mut BufWriter::new(&mut file))?; // write to tmp file

//             let out = self.run(&DEFAULT_VAMPIRE_ARGS, file.path())?; // run vampire
//             trace!("saving vampire's output");
//             ret.push(out);
//             let out = ret.last().unwrap(); // we just pushed to the array

//             if let Some(p) = save_to {
//                 let name = p.join(file.path().file_name().unwrap()); // can't end in ".."
//                 trace!("copying file to {name:?}");
//                 std::fs::copy(file.path(), name)?;
//             }

//             let new_instances_str = match out {
//                 VampireOutput::Unsat(_) => return Ok(ret),
//                 VampireOutput::TimeOut(out) => out,
//             };

//             // find new instances
//             let new_instances = pbl
//                 .crypto_assertions()
//                 .iter()
//                 .map(|ca| ca.search_instances(new_instances_str, env))
//                 .flatten()
//                 .collect_vec();
//             if new_instances.is_empty() {
//                 // no new instances, no need to try again
//                 bail!("no new instances")
//             }

//             let max_var_no_instances = pbl.max_var_no_extras();
//             if cfg!(debug_assertions) {
//                 let str = new_instances.iter().map(|t| format!("{:}", t)).join(", ");
//                 debug!("instances found ({:?}):\n\t[{:}]", new_instances.len(), str)
//             }
//             let n_new_instances = pbl.extend_extra_instances(
//                 new_instances
//                     .into_iter()
//                     .map(|t| t.translate_vars(max_var_no_instances).into()),
//             );

//             if n_new_instances == 0 {
//                 // if all the instances were found before, we bail
//                 bail!("no new instances")
//             }
//         }

//         bail!("ran out of tries (at most {n})")
//     }
// }

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

impl VampireOutput {
    /// Returns `true` if the vampire output is [`TimeOut`].
    ///
    /// [`TimeOut`]: VampireOutput::TimeOut
    #[must_use]
    pub fn is_time_out(&self) -> bool {
        matches!(self, Self::TimeOut(..))
    }

    /// Returns `true` if the vampire output is [`Unsat`].
    ///
    /// [`Unsat`]: VampireOutput::Unsat
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat(..))
    }
}
