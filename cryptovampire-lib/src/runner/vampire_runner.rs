use anyhow::{bail, Context};
use std::{
    io::Write,
    path::PathBuf,
    process::{Command, Stdio},
    usize,
};
use thiserror::Error;
use utils::implvec;

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
    use crate::runner::vampire_runner::ToArgs;
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

impl VampireExec {
    pub fn run<'a>(
        &'a self,
        args: implvec!(&'a VampireArg),
        pbl: &str,
    ) -> anyhow::Result<VampireOutput> {
        let mut cmd = Command::new(&self.location);
        for arg in self.extra_args.iter().chain(args.into_iter()) {
            let [a, b] = arg.to_args();
            cmd.arg(a.as_ref()).arg(b.as_ref());
        }

        let mut child = cmd
            .stdin(Stdio::piped()) // We want to write to stdin
            .stdout(Stdio::piped()) // Capture the stdout
            .spawn()
            .with_context(|| format!("Failed to start vampire ({:?})", &self.location))?;

        // Get the stdin handle of the child process
        if let Some(mut stdin) = child.stdin.take() {
            // Write the content to stdin
            stdin.write_all(pbl.as_bytes()).with_context(|| {
                format!("Failed to write to vampire ({:?})'s stdin", &self.location)
            })?;
        } else {
            bail!("Failed to open vampire ({:?})'s stdin", &self.location)
        }

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
            SUCCESS_RC => Ok(VampireOutput::Unsat(stdout)),
            TIMEOUT_RC => Ok(VampireOutput::TimeOut(stdout)),
            _ => Err(VampireError::UnknownError {
                cmd: format!("{:?}", cmd),
                stdout,
                return_code,
            })?,
        }
    }
}
