use std::borrow::Borrow;
use std::ops::Deref;
use std::path::{Path, PathBuf};

use anyhow::{Context, bail};
use bon::Builder;
use cryptovampire_smt::Smt;
use log::trace;
use tokio::process::Command;
use utils::implvec;

mod bounded_model;
mod regular;
/// Re-exports the `BounededVampire` struct, representing a bounded SMT solver configuration.
pub use bounded_model::BounededVampire;
/// Re-exports the `RegularVampire` struct, representing a regular SMT solver configuration.
pub use regular::RegularVampire;

use crate::runners::SharedProblem;
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
    // /// Should the smt file be kept once we don't need it anymore?
    // #[builder(default = cfg!(debug_assertions))]
    // keep_file: bool,
    #[builder(default = "Termination reason: Refutation\n", into)]
    success_verification: String,
}

impl<S> VampireExecBuilder<S>
where
    S: vampire_exec_builder::State,
{
    /// Extends the arguments of the Vampire executable with additional `VampireArg`s.
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
  ($(#[$other:meta] $variant:ident($name:literal, $content:ty)),*,) => {
      #[allow(dead_code)]
      #[doc = "arguments to [VampireExec] in type-safeish mode"]
      #[derive(Debug, Clone)]
      pub enum VampireArg {
        $(#[$other]  $variant($content)),*
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
    /// Sets the number of cores for Vampire to use.
    Cores("cores", u64),
    /// Sets the memory limit for Vampire in megabytes.
    MemoryLimit("memory_limit", u64),
    /// Sets the operational mode for Vampire.
    Mode("mode", vampire_suboptions::Mode),
    /// Sets the slowness factor for Vampire.
    Slowness("slowness", u64),
    /// Sets the time limit for Vampire in seconds.
    TimeLimit("time_limit", f64),
    /// Sets the input syntax for Vampire.
    InputSyntax("input_syntax", vampire_suboptions::InputSyntax),
    /// Enables or disables new CNF conversion in Vampire.
    NewCnf("newcnf", bool),
    /// Sets the saturation algorithm for Vampire.
    SaturationAlgorithm(
        "saturation_algorithm",
        vampire_suboptions::SaturationAlgorithm
    ),
    /// Enables or disables Avatar mode in Vampire.
    Avatar("avatar", bool),
    /// Sets the SAT solver to be used by Vampire.
    SatSolver("sat_solver", vampire_suboptions::SatSolver),
    /// Enables or disables showing new clauses in Vampire.
    ShowNew("show_new", bool),
    /// Enables or disables inlining of let expressions in Vampire.
    InlineLet("inline_let", bool),
);

pub mod vampire_suboptions {
    use super::ToArgs;
    macro_rules! suboptions {
      ($name:ident, $( $(#[$other:meta])?($variant:ident, $content:literal)),*,) => {
          #[allow(dead_code)]
          #[derive(Debug, Clone, Eq, Ord, PartialEq, PartialOrd, Hash, Copy)]
          pub enum $name {
            $($(#[$other])? $variant),*
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

    suboptions!(Mode,
        /// Portfolio mode.
        (Portfolio, "portfolio"),
    );
    suboptions!(
        InputSyntax,
        /// SMT-LIB 2 input syntax.
        (SmtLib2, "smtlib2"),
        /// TPTP input syntax.
        (Tptp, "tptp"),
        /// Auto-detect input syntax.
        (Auto, "auto"),
    );
    suboptions!(
        SaturationAlgorithm,
        /// Discount saturation algorithm.
        (Discount, "discount"),
        /// Otter saturation algorithm.
        (Otter, "otter"),
        /// Limited Resources saturation algorithm.
        (LimitedResources, "lrs"),
        /// Finite Model Builder saturation algorithm.
        (FiniteModel, "fmb"),
        /// Z3 saturation algorithm.
        (Z3, "z3"),
    );
    suboptions!(SatSolver,
        /// Minisat SAT solver.
        (Minisat, "minisat"),
        /// Z3 SAT solver.
        (Z3, "z3"),
    );
}

/// Turn something into an array of [str] for the [Command] object
/// A trait for converting types into an array of strings for command-line arguments.
trait ToArgs<const N: usize> {
    /// Converts the implementor into an array of `N` strings, representing command-line arguments.
    fn to_args(&self) -> [String; N];
}

impl ToArgs<1> for u64 {
    /// Converts a `u64` into a single string argument.
    fn to_args(&self) -> [String; 1] {
        [self.to_string()]
    }
}

impl ToArgs<1> for f64 {
    /// Converts an `f64` into a single string argument.
    fn to_args(&self) -> [String; 1] {
        [self.to_string()]
    }
}

impl ToArgs<1> for bool {
    /// Converts a `bool` into a single string argument ("on" for true, "off" for false).
    fn to_args(&self) -> [String; 1] {
        [if *self { "on" } else { "off" }.into()]
    }
}

/// Success return code
const SUCCESS_RC: i32 = 0;
/// Timeout return code
const TIMEOUT_RC: i32 = 1;

impl VampireExec {
    pub fn contains_time(&self) -> bool {
        self.args
            .iter()
            .any(|x| matches!(&x, VampireArg::TimeLimit(_)))
    }

    /// Runs the Vampire executable with the given SMT file.
    ///
    /// Returns `Ok(true)` if Vampire proves the query (refutation found),
    /// `Ok(false)` if it disproves it, or `Err` if Vampire encounters an error.
    pub async fn run(&self, pbl: &Problem, file: &Path) -> anyhow::Result<bool> {
        let mut cmd = Command::new(&self.exe_location);
        cmd.args(self.args.iter().flat_map(|x| x.to_args().into_iter()));

        if !self.contains_time() {
            cmd.args(VampireArg::TimeLimit(pbl.config.vampire_timeout.as_secs_f64()).to_args());
        }

        cmd.arg(file);
        cmd.kill_on_drop(true);

        #[cfg(debug_assertions)]
        {
            eprintln!("running '{:?}'...", cmd.as_std())
        }

        let o = cmd.output().await?;

        tr!("status code: {:?}", o.status.code());
        let refutation = std::str::from_utf8(&o.stdout)
            .with_context(|| "non utf8 ouput")?
            .contains(&self.success_verification);
        tr!("refutation: {refutation}");

        if o.status.code() != Some(SUCCESS_RC)
            && o.status.code() != Some(TIMEOUT_RC)
            && o.status.code().is_some()
        {
            eprintln!("file: {file:?}");
            eprintln!(
                "stdout:\n{}",
                std::str::from_utf8(&o.stdout).with_context(|| "non utf8 stdout")?
            );
            eprintln!(
                "sterr:\n{}",
                std::str::from_utf8(&o.stderr).with_context(|| "non utf8 stderr")?
            );
            eprintln!("vampire failed with error code {:?}", o.status.code());
            bail!(
                "stdout:\n{}\nsterr:\n{}",
                std::str::from_utf8(&o.stdout).unwrap(),
                std::str::from_utf8(&o.stderr).unwrap(),
            )
        }

        Ok(o.status.success() && refutation)
    }

    /// Writes the given SMT statements to a temporary file and runs Vampire on it.
    ///
    /// If `keep_file` is true, the temporary file is not deleted after execution.
    pub async fn run_smt<RefS>(&self, pbl: &Problem, smt: implvec!(RefS)) -> anyhow::Result<bool>
    where
        RefS: Borrow<MSmt>,
    {
        let mut tmpfile = tempfile::Builder::new()
            .prefix("cryptovampire")
            .suffix(".smt")
            .keep(pbl.config.keep_smt_files)
            .tempfile()?;

        if pbl.config.keep_smt_files {
            println!("writting smt file to '{:?}' ...", tmpfile.path())
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
                writeln!(buffer, "{}", statement.as_pretty())?;
            }
        }

        if pbl.config.keep_smt_files {
            tr!("file written")
        }

        self.run(pbl, tmpfile.path()).await
    }

    /// Runs Vampire with the given SMT query, incorporating the problem's SMT prelude.
    ///
    /// This method prepares the SMT input by adding the prelude and the query,
    /// then executes Vampire and interprets its result.
    pub async fn run_smt_with_pbl<'a>(
        &self,
        pbl: &SharedProblem<'a>,
        query: MSmtFormula,
    ) -> anyhow::Result<Option<bool>> {
        trace!("checking {query}");
        let mut prelude = Vec::new();
        pbl.extend_smt_prelud(&mut prelude).await;
        prelude.extend([Smt::mk_query(query), Smt::CheckSat]);
        // let pbl: &Problem<_> = &self.pbl.borrow();
        let res = self
            .run_smt(Deref::deref(&pbl.0.read().await), prelude)
            .await
            .with_context(|| "something went wrong with vampire")?;

        if res { Ok(Some(true)) } else { Ok(None) }
    }
}

/// Discovers the path to the Vampire executable in the system's `$PATH`.
///
/// # Panics
///
/// Panics if the `vampire` executable cannot be found in `$PATH`.
fn get_vampire_location() -> PathBuf {
    which::which("vampire").expect("can't find vampire in the $PATH")
}
