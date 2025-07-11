use std::borrow::Borrow;
use std::fmt::Display;
use std::path::{Path, PathBuf};
use std::process::Command;

use bon::Builder;
use cryptovampire_smt::Smt;
use golgge::Dependancy;
use itertools::chain;
use log::trace;
use utils::implvec;

use crate::{MSmtFormula, Problem};

declare_trace!($"vampire_exec");

/// The [Runner] itself
#[derive(Debug, Clone, Builder)]
pub struct VampireExec {
    /// The location of the vampire executable
    ///
    /// By default it looks into the `$PATH`
    #[builder(default = which::which("vampire").unwrap(), into)]
    exe_location: PathBuf,
    /// Arguments to vampire
    #[builder(default = VampireExec::default_args(), with = <_>::from_iter)]
    args: Vec<VampireArg>,
    /// Should the smt file be kept once we don't need it anymore?
    #[builder(default = false)]
    keep_file: bool,
}

macro_rules! options {
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

options!(
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
    macro_rules! suboptions {
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

    suboptions!(Mode, (Portfolio, "portfolio"),);
    suboptions!(
        InputSyntax,
        (SmtLib2, "smtlib2"),
        (Tptp, "tptp"),
        (Auto, "auto"),
    );
    suboptions!(
        SaturationAlgorithm,
        (Discount, "discount"),
        (Otter, "otter"),
        (LimitedResources, "lrs"),
        (FiniteModel, "fmb"),
        (Z3, "z3"),
    );
    suboptions!(SatSolver, (Minisat, "minisat"), (Z3, "z3"),);
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
        cmd.args(self.args.iter().flat_map(|x| x.to_args().into_iter()));
        cmd.arg(file);

        tr!("running '{:?}'...", cmd);

        let o = cmd.output()?;

        tr!("status code: {:?}", o.status.code());
        let refutation = std::str::from_utf8(&o.stdout)
            .unwrap()
            .contains("Termination reason: Refutation\n");
        tr!("refutation: {refutation}");

        if o.status.code() != Some(SUCCESS_RC) && o.status.code() != Some(TIMEOUT_RC) {
            eprintln!("failed with error code {:}", o.status.code().unwrap());
            eprintln!("stdout:\n{}", std::str::from_utf8(&o.stdout).unwrap());
            eprintln!("sterr:\n{}", std::str::from_utf8(&o.stderr).unwrap());
            panic!()
        }

        Ok(o.status.success() && refutation)
    }

    pub fn run_smt<S, F, RefS>(&self, smt: implvec!(RefS)) -> anyhow::Result<bool>
    where
        S: Display,
        F: Display,
        RefS: Borrow<Smt<S, F>>,
    {
        let mut tmpfile = tempfile::Builder::new()
            .prefix("cryptovampire")
            .suffix(".smt")
            .keep(self.keep_file)
            .tempfile()?;

        if self.keep_file {
            tr!("writting smt file to '{:?}' ...", tmpfile.path())
        }

        {
            use std::io::Write as _;
            let buffer = tmpfile.as_file_mut();
            let mut i = 1;
            for statement in smt {
                let statement = statement.borrow();
                if statement.is_any_assert() {
                    writeln!(buffer, "; {i:}")?;
                    i += 1;
                }
                if self.keep_file {
                    let pretty = statement.as_pretty();
                    writeln!(buffer, "{pretty}")?;
                } else {
                    writeln!(buffer, "{statement}")?;
                }
            }
        }

        if self.keep_file {
            tr!("file written")
        }

        self.run(tmpfile.path())
    }

    pub fn default_args() -> Vec<VampireArg> {
        vec![
            VampireArg::Cores(0),
            VampireArg::Mode(vampire_suboptions::Mode::Portfolio),
            VampireArg::InputSyntax(vampire_suboptions::InputSyntax::SmtLib2),
            VampireArg::TimeLimit(5.0),
        ]
    }

    pub fn run_to_dependancy(&self, pbl: &mut Problem, query: MSmtFormula) -> Dependancy {
        trace!("checking {query}");
        let prelude = pbl.get_smt_prelude();
        // let pbl: &Problem<_> = &self.pbl.borrow();
        let res = self
            .run_smt(chain![
                prelude.iter().cloned(),
                [Smt::mk_query(query), Smt::CheckSat]
            ])
            .expect("something went wrong with vampire");

        if res {
            Dependancy::axiom()
        } else {
            Dependancy::impossible()
        }
    }
}
