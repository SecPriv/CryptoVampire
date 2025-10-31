//! Some functions to help building and using [Runner]
use std::io::Read;
use std::process::{Command, Stdio};

use log::trace;

use super::{Runner, RunnerHandler};
use crate::error::{BaseContext, CVContext};

#[derive(Debug)]
pub enum RetCodeAndStdout {
    Success { stdout: String, return_code: i32 },
    Killed { stdout: String },
}

pub fn exec_cmd<R, H>(runner: &R, handler: H, cmd: &mut Command) -> crate::Result<RetCodeAndStdout>
where
    H: RunnerHandler,
    R: Runner,
{
    cmd.stdout(Stdio::piped()) // instead of piped, this lets us wait on the child
        // .stdin(Stdio::null())
        // .stderr(Stdio::null())
        ;
    let child = handler.spawn_child(cmd, runner.kind())?;
    // .with_context(|| format!("Failed to start {} ($ {cmd:?})", R::name()))?;

    trace!("process spawned, reading the output till EOF");
    // take the stdout
    let stdout = {
        let mut out = String::default();
        child
            .take_stdout()
            .with_message(|| "couldn't build the stdout handle")?
            // stdout
            .read_to_string(&mut out)
            .no_location()?;
        // .map(|mut s| s.read_to_string(&mut out))
        // .transpose()
        // .with_context(|| format!("{}'s output isn't in utf-8 ($ {cmd:?})", R::name()))?;
        // drops and close the
        out
    };
    // The process should have ended by now but we still wait for it to get the exit status
    trace!("waiting for {cmd:?}");
    let exit_status = child.wait()?;
    trace!("done waiting for {cmd:?}");

    let return_code = match exit_status.code() {
        Some(c) => c,
        None => return Ok(RetCodeAndStdout::Killed { stdout }),
    };
    trace!(
        "process ended successfully ({cmd:?})\n\tstout:\n{}",
        save_stdout(&stdout)
    );
    Ok(RetCodeAndStdout::Success {
        stdout,
        return_code,
    })
}

/// tries to save to a temporary file
fn save_stdout(stdout: &String) -> String {
    let maybe_file = tempfile::Builder::new()
        .prefix("solver_output_")
        .suffix(".txt")
        .keep(true)
        .tempfile()
        .map_err(|_| ())
        .and_then(|mut file| {
            use std::io::Write;
            let test = write!(&mut file, "{stdout}");
            test.map_err(|_| ()).map(|_| file)
        });
    let stdout_msg = match maybe_file.as_ref() {
        Ok(f) => {
            let path = f.path().as_os_str();
            format!("file: {path:?}")
        }
        Err(_) => stdout.clone(),
    };
    stdout_msg
}

/// simplified, object safe version of [Runner] and [Discoverer]
pub mod dyn_traits {
    use std::any::Any;
    use std::path::Path;

    use crate::environement::environement::Environement;
    use crate::error::BaseContext;
    use crate::problem::Problem;
    use crate::problem::crypto_assumptions::CryptoAssumption;
    use crate::runner::searcher::InstanceSearcher;
    use crate::runner::{Discoverer, Runner, RunnerHandler, RunnerOut};

    pub type RunnerOutDyn = RunnerOut<
        Box<dyn Any + Send>,
        Box<dyn Any + Send>,
        Box<dyn Any + Send>,
        Box<dyn Any + Send>,
    >;

    pub trait DynRunner<R>
    where
        R: RunnerHandler + Clone,
    {
        fn dyn_run_to_tmp<'bump>(
            &self,
            handler: R,
            env: &Environement<'bump>,
            pbl: &Problem<'bump>,
            save_to: Option<&Path>,
        ) -> crate::Result<RunnerOutDyn>;
    }

    pub trait DynDiscoverer<R>: DynRunner<R>
    where
        R: RunnerHandler + Clone,
    {
        fn dyn_discover<'bump>(
            &self,
            env: &Environement<'bump>,
            pbl: &mut Problem<'bump>,
            out: &dyn Any,
        ) -> crate::Result<()>;
    }

    /// I wanted to have [DynRunner] and [DynDiscoverer] in a single [Vec],
    /// hence the enum
    pub enum RunnerAndDiscoverer<R: RunnerHandler + Clone> {
        Runner(Box<dyn DynRunner<R> + Sync>),
        Discoverer(Box<dyn DynDiscoverer<R> + Sync>),
    }

    impl<R> DynRunner<R> for RunnerAndDiscoverer<R>
    where
        R: RunnerHandler + Clone,
    {
        fn dyn_run_to_tmp<'a, 'bump>(
            &self,
            handler: R,
            env: &Environement<'bump>,
            pbl: &Problem<'bump>,
            save_to: Option<&Path>,
        ) -> crate::Result<RunnerOutDyn> {
            match self {
                RunnerAndDiscoverer::Runner(r) => r.dyn_run_to_tmp(handler, env, pbl, save_to),
                RunnerAndDiscoverer::Discoverer(d) => d.dyn_run_to_tmp(handler, env, pbl, save_to),
            }
        }
    }

    impl<R, T> DynRunner<R> for T
    where
        T: Runner,
        R: RunnerHandler + Clone,
        T::SatR: Sync + Send + 'static,
        T::UnsatR: Sync + Send + 'static,
        T::TimeoutR: Sync + Send + 'static,
        T::OtherR: Sync + Send + 'static,
    {
        fn dyn_run_to_tmp<'a, 'bump>(
            &self,
            handler: R,
            env: &Environement<'bump>,
            pbl: &Problem<'bump>,
            save_to: Option<&Path>,
        ) -> crate::Result<RunnerOutDyn> {
            Ok(self
                .run_to_tmp(handler, env, pbl, self.default_args(), save_to)?
                .into_dyn())
        }
    }

    impl<R, T> DynDiscoverer<R> for T
    where
        T: Discoverer,
        R: RunnerHandler + Clone,
        for<'bump> CryptoAssumption<'bump>: InstanceSearcher<'bump, T>,
        T::SatR: Sync + Send + 'static,
        T::UnsatR: Sync + Send + 'static,
        T::TimeoutR: Sync + Send + 'static,
        T::OtherR: Sync + Send + 'static,
    {
        fn dyn_discover<'bump>(
            &self,
            env: &Environement<'bump>,
            pbl: &mut Problem<'bump>,
            out: &dyn Any,
        ) -> crate::Result<()> {
            let out: &<Self as Runner>::TimeoutR =
                out.downcast_ref().with_message(|| "not the right type")?;

            self.discover(env, pbl, out)
        }
    }
}
