use std::{io::Read, process::Command};

use anyhow::Context;

use super::{runner::ChildKind, RunnerHandler};

#[derive(Debug)]
pub struct RetCodeAndStdout {
    pub stdout: String,
    pub return_code: i32,
}

pub fn run_cmd<H>(
    handler: H,
    cmd: &mut Command,
    kind: ChildKind,
) -> anyhow::Result<RetCodeAndStdout>
where
    H: RunnerHandler,
{
    let child = handler
        .spawn_child(cmd, kind)
        .with_context(|| format!("Failed to start ($ {cmd:?})"))?;

    // wait for the proccess
    let exit_status = child.wait()?;

    // read the output from the process
    let stdout = {
        let mut out = String::default();
        child
            .take_stdout()
            .map(|mut s| s.read_to_string(&mut out))
            .transpose()
            .with_context(|| format!("output isn't in utf-8 ($ {cmd:?})"))?;
        out
    };
    let return_code = exit_status
        .code()
        .with_context(|| format!("terminated by signal.\n\t$ {cmd:?}\n\tstoud:\n{stdout}"))?;
    Ok(RetCodeAndStdout {
        stdout,
        return_code,
    })
}
