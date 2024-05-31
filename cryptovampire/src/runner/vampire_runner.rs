use std::{
    io::Write,
    process::{Command, Stdio},
    usize,
};

#[derive(Debug, Clone)]
pub struct VampireExec {
    location: String,
}

trait ToArgs<const N: usize> {
    fn to_args(&self) -> [Box<str>; N];
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
    TimeLimit("time_limit", u64),
    InputSyntax("input_syntax", vampire_suboptions::InputSyntax),
    NewCnf("newcnf", bool),
    SaturationAlgorithm(
        "saturation_algorithm",
        vampire_suboptions::SaturationAlgorithm
    ),
    Avatar("avatar", bool),
    SatSolver("sat_solver", vampire_suboptions::SatSolver),
    ShowNew("show_new", bool),
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

impl VampireExec {
    pub fn run(&self, args: &[VampireArg], pbl: &str) -> anyhow::Result<String> {
        let mut cmd = Command::new(&self.location);
        for arg in args {
            let [a, b] = arg.to_args();
            cmd.arg(a.as_ref()).arg(b.as_ref());
        }

        let mut child = cmd
            .stdin(Stdio::piped()) // We want to write to stdin
            .stdout(Stdio::piped()) // Capture the stdout
            .spawn()?;

        // Get the stdin handle of the child process
        if let Some(mut stdin) = child.stdin.take() {
            // Write the content to stdin
            stdin.write_all(pbl.as_bytes())?;
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "Failed to open stdin",
            ))?;
        }

        // Optionally, you can read the output from the process
        let output = child.wait_with_output()?;

        // Print the output
        Ok(String::from_utf8(output.stdout)?)
    }
}

impl Default for VampireExec {
    fn default() -> Self {
        Self {
            location: "vampire".into(),
        }
    }
}
