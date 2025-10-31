use std::borrow::Borrow;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, bail};
use bon::{Builder, bon, builder};
use cryptovampire_smt::Smt;
use golgge::Dependancy;
use itertools::chain;
use log::trace;
use utils::implvec;

mod bounded_model;
mod regular;
pub use bounded_model::BounededVampire;
pub use regular::RegularVampire;

use crate::{MSmt, MSmtFormula, Problem};

declare_trace!($"vampire_exec");

/// The [Runner] itself
#[derive(Debug, Clone, Builder)]
#[builder(builder_type = VampireExecBuilder)]
struct VampireExec {
    /// Arguments to vampire
    #[builder(field = vec![])]
    args: Vec<VampireArg>,
    /// The location of the vampire executable
    ///
    /// By default it looks into the `$PATH`
    #[builder(default = get_vampire_location(), into)]
    exe_location: PathBuf,
    /// Should the smt file be kept once we don't need it anymore?
    #[builder(default = cfg!(debug_assertions))]
    keep_file: bool,

    #[builder(default = "Termination reason: Refutation\n", into)]
    success_verification: String,
}

impl<S> VampireExecBuilder<S>
where
    S: vampire_exec_builder::State,
{
    pub fn with_pbl(self, pbl: &Problem) -> VampireExecBuilder<vampire_exec_builder::SetKeepFile<S>>
    where
        S::KeepFile: vampire_exec_builder::IsUnset,
    {
        self.keep_file(pbl.config.keep_smt_files)
            .timeout(pbl.config.vampire_timeout)
    }

    pub fn extend_args(mut self, args: implvec!(VampireArg)) -> Self {
        self.args.extend(args);
        self
    }

    /// sets the timeout in seconds
    pub fn timeout(mut self, timeout: ::std::time::Duration) -> Self {
        let narg = VampireArg::TimeLimit(timeout.as_secs_f64());
        if let Some(arg) = self.args.iter_mut().find(|x| x.same(&narg)) {
            *arg = narg;
        } else {
            self.args.push(narg);
        }
        self
    }
}

macro_rules! options {
  ($($variant:ident($name:literal, $content:ty)),*,) => {
      #[allow(dead_code)]
      #[doc = "arguments to [VampireExec] in type-safeish mode"]
      #[derive(Debug, Clone)]
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

    impl VampireArg {
        #[doc = "tells if two [VampireArg] are setting the same parameter"]
        pub const fn same(&self, other: &Self) -> bool {
            matches!(
                (self, other),
                    $((Self::$variant(..), Self::$variant(..)) )|*
            )
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

        #[cfg(debug_assertions)]
        {
            eprintln!("running '{:?}'...", cmd)
        }

        let o = cmd.output()?;

        tr!("status code: {:?}", o.status.code());
        let refutation = std::str::from_utf8(&o.stdout)
            .unwrap()
            .contains(&self.success_verification);
        tr!("refutation: {refutation}");

        if o.status.code() != Some(SUCCESS_RC) && o.status.code() != Some(TIMEOUT_RC) {
            eprintln!(
                "vampire failed with error code {:}",
                o.status.code().unwrap()
            );
            eprintln!("file: {file:?}");
            eprintln!("stdout:\n{}", std::str::from_utf8(&o.stdout).unwrap());
            eprintln!("sterr:\n{}", std::str::from_utf8(&o.stderr).unwrap());
            bail!(
                "stdout:\n{}\nsterr:\n{}",
                std::str::from_utf8(&o.stdout).unwrap(),
                std::str::from_utf8(&o.stderr).unwrap(),
            )
        }

        Ok(o.status.success() && refutation)
    }

    pub fn run_smt<RefS>(&self, smt: implvec!(RefS)) -> anyhow::Result<bool>
    where
        RefS: Borrow<MSmt>,
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

    // pub fn default_args() -> Vec<VampireArg> {
    //     vec![
    //         VampireArg::Cores(0),
    //         VampireArg::Mode(vampire_suboptions::Mode::Portfolio),
    //         VampireArg::InputSyntax(vampire_suboptions::InputSyntax::SmtLib2),
    //     ]
    // }

    pub fn run_smt_with_pbl(
        &self,
        pbl: &mut Problem,
        query: MSmtFormula,
    ) -> anyhow::Result<Option<bool>> {
        trace!("checking {query}");
        let prelude = pbl.get_smt_prelude();
        // let pbl: &Problem<_> = &self.pbl.borrow();
        let res = self
            .run_smt(chain![
                prelude.iter().cloned(),
                [Smt::mk_query(query), Smt::CheckSat]
            ])
            .with_context(|| "something went wrong with vampire")?;

        if res { Ok(Some(true)) } else { Ok(None) }
    }
}

fn get_vampire_location() -> PathBuf {
    which::which("vampire").expect("can't find vampire in the $PATH")
}
