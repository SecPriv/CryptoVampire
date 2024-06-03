use anyhow::{anyhow, bail};
use cryptovampire_lib::{environement::environement::Environement, problem::Problem};
use itertools::Itertools;
use searcher::InstanceSearcher;
use vampire_runner::VampireExec;

use crate::smt::smt::SmtFile;
mod searcher;
mod tmpformula;
mod vampire_runner;

pub fn run_multiple_time<'bump>(
    ntimes: u32,
    vampire: VampireExec,
    env: &Environement<'bump>,
    mut pbl: Problem<'bump>,
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

        let tmp = pbl
            .crypto_assertions
            .iter()
            .map(|ca| ca.search_instances(&to_search, env))
            .collect_vec();
        let max_var_no_instances = pbl.max_var_no_extras();
        pbl.extra_instances.extend(
            tmp.into_iter()
                .flatten()
                .map(|t| t.translate_vars(max_var_no_instances).into()),
        )
    }

    Err(anyhow!("Ran out of tries"))
}
