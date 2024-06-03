use anyhow::{anyhow, bail};
use cryptovampire_lib::{environement::environement::Environement, problem::Problem};
use vampire_runner::VampireExec;

use crate::smt::smt::SmtFile;
mod tmpformula;
mod vampire_runner;
mod searcher;

pub fn run_multiple_time<'bump>(
    ntimes: u32,
    vampire: VampireExec,
    env: &Environement<'bump>,
    pbl: Problem<'bump>,
) -> anyhow::Result<String> {
    if ntimes == 0 {}
    let n = if ntimes == 0 { u32::MAX } else { ntimes };

    for _ in 0..n {
        let smt = SmtFile::from_general_file(env, pbl.into_general_file(&env))
            .as_diplay(env)
            .to_string();
        let out = vampire.run([], &smt)?;
        let to_search = match out {
            vampire_runner::VampireOutput::Unsat(proof) => return Ok(proof),
            vampire_runner::VampireOutput::TimeOut(out) => out,
        };
    }

    Err(anyhow!("Ran out of tries"))
}
