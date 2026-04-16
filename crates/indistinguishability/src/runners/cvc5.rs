use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{Context, bail};
use bon::Builder;
use cryptovampire_smt::{CVC5, Smt};
use log::trace;
use tokio::process::Command;
use utils::implvec;

use crate::runners::{Runner, never_end};
use crate::{MSmt, MSmtFormula, Problem};

declare_trace!($"cvc5_exec");

/// The [Runner] itself
#[derive(Debug, Clone, Builder)]
#[builder(builder_type = Cvc5ExecBuilder)]
pub struct Cvc5Exec {
    /// Arguments to cvc5
    #[builder(field = vec![])]
    args: Vec<Cvc5Arg>,
    /// The location of the cvc5 executable
    ///
    /// By default it looks into the `$PATH`
    #[builder(default = get_cvc5_location(), into)]
    exe_location: PathBuf,
    #[builder(default = "unsat\n", into)]
    success_verification: String,
}

impl<S> Cvc5ExecBuilder<S>
where
    S: cvc5_exec_builder::State,
{
    /// Extends the arguments of the Cvc5 executable with additional `Cvc5Arg`s.
    pub fn default_args(self) -> Self {
        use Cvc5Arg::*;
        self
    }

    /// Extends the arguments of the Cvc5 executable with additional `Cvc5Arg`s.
    #[allow(dead_code)]
    pub fn extend_args(mut self, args: implvec!(Cvc5Arg)) -> Self {
        self.args.extend(args);
        self
    }

    /// sets the timeout in seconds
    #[allow(unused)]
    pub fn timeout(mut self, timeout: ::std::time::Duration) -> Self {
        let timeout_arg = Cvc5Arg::Tlim(timeout.as_millis() as u64);
        if let Some(arg) = self.args.iter_mut().find(|x| x.same(&timeout_arg)) {
            *arg = timeout_arg;
        } else {
            self.args.push(timeout_arg);
        }
        self
    }
}

macro_rules! options {
  ($($(#[$other:meta])* $variant:ident($name:literal, $content:ty)),*$(,)?) => {
      #[allow(dead_code)]
      #[doc = "arguments to [Cvc5Exec] in type-safeish mode"]
      #[derive(Debug, Clone)]
      pub enum Cvc5Arg {
        $($(#[$other])*  $variant($content)),*
      }

      impl ToArgs<1> for Cvc5Arg {
        fn to_args(&self) -> [String;1] {
          match self {
            $(Self::$variant(x) => {let [y] = x.to_args(); [format!("--{}={}", $name, y)]})*
          }
        }
      }

    impl Cvc5Arg {
        #[doc = "tells if two [Cvc5Arg] are setting the same parameter"]
        #[allow(unused)]
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
    /// Sets the time limit for Cvc5 in milliseconds.
    Tlim("tlimit", u64),
);

/// Turn something into an array of [str] for the [Command] object
trait ToArgs<const N: usize> {
    /// Converts the implementor into an array of `N` strings, representing command-line arguments.
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
        [if *self { "true" } else { "false" }.into()]
    }
}

impl ToArgs<1> for String {
    fn to_args(&self) -> [String; 1] {
        [self.clone()]
    }
}

/// Success return code
const SUCCESS_RC: i32 = 0;
/// Timeout return code
const TIMEOUT_RC: i32 = 1;

impl Cvc5Exec {
    pub fn contains_time(&self) -> bool {
        self.args.iter().any(|x| matches!(&x, Cvc5Arg::Tlim(_)))
    }

    /// Runs the Cvc5 executable with the given SMT file.
    ///
    /// Returns `Ok(true)` if Cvc5 proves the query (unsat found),
    /// `Ok(false)` if it disproves it (sat), or `Err` if Cvc5 encounters an error.
    pub async fn run(&self, pbl: &Problem, file: &Path) -> anyhow::Result<bool> {
        let mut cmd = Command::new(&self.exe_location);
        cmd.args(self.args.iter().flat_map(|x| x.to_args().into_iter()));

        if !self.contains_time() {
            let timeout = pbl.config.smt_timeout;
            cmd.args(Cvc5Arg::Tlim(timeout.as_millis() as u64).to_args());
        }

        cmd.arg(file);
        cmd.kill_on_drop(true);

        #[cfg(debug_assertions)]
        {
            eprintln!("running '{:?}'...", cmd.as_std())
        }

        let o = cmd.output().await?;

        tr!("status code: {:?}", o.status.code());
        let output = std::str::from_utf8(&o.stdout).with_context(|| "non utf8 ouput")?;
        tr!("cvc5 output: {}", output);

        // Check for unknown - loop forever if unknown
        if output.contains("unknown") {
            never_end().await
        }

        let success = output.contains(&self.success_verification);
        tr!("success (unsat): {success}");

        if o.status.code() != Some(SUCCESS_RC)
            && o.status.code() != Some(TIMEOUT_RC)
            && o.status.code().is_some()
        {
            bail!(
                "cvc5 failed in '{file:?}' with error code \
                 {:?}\nstdout:\n```\n{}\n```\nsterr:\n```\n{}\n```",
                o.status.code(),
                String::from_utf8_lossy(&o.stdout),
                String::from_utf8_lossy(&o.stderr)
            )
        }

        Ok(success)
    }
}

/// Discovers the path to the Cvc5 executable in the system's `$PATH`.
///
/// # Panics
///
/// Panics if the `cvc5` executable cannot be found in `$PATH`.
fn get_cvc5_location() -> PathBuf {
    if let Some(path) = option_env!("CVC5_PATH") {
        path.into()
    } else {
        which::which("cvc5").expect("can't find cvc5 in the $PATH")
    }
}

impl Runner for Cvc5Exec {
    async fn try_run(&self, pbl: &Problem, query: &Path) -> anyhow::Result<Option<bool>> {
        match self.run(pbl, query).await? {
            true => Ok(Some(true)),
            false => Ok(None),
        }
    }

    fn mut_splitter<'a, U>(&self, spliter: &'a mut super::RunnerSplitter<U>) -> Option<&'a mut U> {
        spliter.cvc5.as_mut()
    }

    fn get_sover_kind(&self) -> cryptovampire_smt::SolverKind {
        CVC5
    }
}
