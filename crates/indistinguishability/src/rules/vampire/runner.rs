use std::{
    path::{Path, PathBuf},
    process::Command,
};

/// The [Runner] itself
#[derive(Debug, Clone)]
pub struct VampireExec {
    pub exe_location: PathBuf,
    pub extra_args: Vec<VampireArg>,
}

macro_rules! option {
  ($($variant:ident($name:literal, $content:ty)),*,) => {
      #[allow(dead_code)]
      #[doc = "arguments to [VampireExec] in type-safeish mode"]
      #[derive(Debug, Clone, PartialEq, PartialOrd)]
      pub enum VampireArg {
        $($variant($content)),*
      }

      impl ToArgs<2> for VampireArg {
        fn to_args(&self) -> [String;2] {
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
    use super::ToArgs;
    macro_rules! suboption {
      ($name:ident, $(($variant:ident, $content:literal)),*,) => {
          #[allow(dead_code)]
          #[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd, Hash, Copy)]
          pub enum $name {
            $($variant),*
          }

          impl ToArgs<1> for $name {
            fn to_args(&self) -> [String;1] {
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
    fn to_args(&self) -> [String; N];
}

impl ToArgs<1> for u64 {
    fn to_args(&self) -> [String; 1] {
        [self.to_string()]
    }
}

impl ToArgs<1> for f64 {
    fn to_args(&self) -> [String; 1] {
        [self.to_string()]
    }
}

impl ToArgs<1> for bool {
    fn to_args(&self) -> [String; 1] {
        [if *self { "on" } else { "off" }.into()]
    }
}

/// Success return code
const SUCCESS_RC: i32 = 0;
/// Timeout return code
const TIMEOUT_RC: i32 = 1;

impl VampireExec {
    pub fn run(&self, file: &Path) -> anyhow::Result<bool> {
        let mut cmd = Command::new(&self.exe_location);
        cmd.args(self.extra_args.iter().flat_map(|x| x.to_args().into_iter()));
        cmd.arg(file);
        let o = cmd.output()?;
        if o.status.code() != Some(SUCCESS_RC) && o.status.code() != Some(TIMEOUT_RC) {
            println!("{}", std::str::from_utf8(&o.stdout).unwrap());
            println!("{:}", o.status.code().unwrap());
            panic!()
        }

        println!(
            "{}",
            std::str::from_utf8(&o.stdout)
                .unwrap()
                .contains("Termination reason: Refutation\n")
        );

        Ok(o.status.success()
            && std::str::from_utf8(&o.stdout)
                .unwrap()
                .contains("Termination reason: Refutation\n"))
    }
}
