use std::{
    io::Read,
    process::{Command, Stdio},
};

use log::trace;

use crate::error::{BaseContext, CVContext};

use super::{Runner, RunnerHandler};

#[derive(Debug)]
pub struct RetCodeAndStdout {
    pub stdout: String,
    pub return_code: i32,
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

    let return_code = exit_status.code().with_message(|| {
        format!(
            "{} terminated by signal.\n\t$ {cmd:?}\n\tstoud:\n{stdout}",
            R::name()
        )
    })?;
    trace!("process ended successfully ({cmd:?})\nstdout: {stdout}");
    Ok(RetCodeAndStdout {
        stdout,
        return_code,
    })
}

pub mod dyn_traits {
    use std::{any::Any, path::Path};

    use crate::{
        environement::environement::Environement,
        error::BaseContext,
        problem::{crypto_assumptions::CryptoAssumption, Problem},
        runner::{searcher::InstanceSearcher, Discoverer, Runner, RunnerHandler, RunnerOut},
    };

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

    pub trait DynDiscovered<R>: DynRunner<R>
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

    pub enum RunnerAndDiscoverer<R: RunnerHandler + Clone> {
        Runner(Box<dyn DynRunner<R> + Sync>),
        Discoverer(Box<dyn DynDiscovered<R> + Sync>),
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

    impl<R, T> DynDiscovered<R> for T
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
