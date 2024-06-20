use std::{
    fs::File,
    io::{BufWriter, Write},
};

use anyhow::{anyhow, bail};
use cryptovampire_lib::{
    environement::environement::{AutomatedVampire, Environement},
    problem::Problem,
};
use itertools::Itertools;
use log::debug;
use searcher::InstanceSearcher;
use vampire_runner::{VampireArg, VampireExec};

use crate::smt::smt::SmtFile;
mod searcher;
mod tmpformula;
pub mod vampire_runner;

pub fn run_multiple_time<'bump>(
    ntimes: u32,
    vampire: &VampireExec,
    env: &Environement<'bump>,
    pbl: &mut Problem<'bump>,
) -> anyhow::Result<String> {
    if ntimes == 0 {}
    let n = if ntimes == 0 { u32::MAX } else { ntimes };

    for i in 0..n {
        debug!("running vampire {:}/{:}...", i, n);
        let smt = SmtFile::from_general_file(env, pbl.into_general_file(&env))
            .as_diplay(env)
            .to_string();
        if let Some(AutomatedVampire {
            smt_debug: Some(smt_debug),
            ..
        }) = env.get_automated_vampire()
        {
            if smt_debug.is_dir() {
                let path = smt_debug.join(format!("{i}.smt"));
                debug!("trying to write to {:?}", path);
                let f = File::options()
                    .write(true)
                    .truncate(true)
                    .create(true)
                    .open(path)?;
                let mut bw = BufWriter::new(f);
                write!(&mut bw, "{smt}")?;
            } else {
                let path_str = smt_debug.to_str().ok_or(anyhow!(
                    "the smt-debug path cannot be converted to a string"
                ))?;
                bail!("{} doesn't exist or is not a directory", path_str)
            }
        }
        let out = vampire.run(
            &[
                VampireArg::InputSyntax(vampire_runner::vampire_suboptions::InputSyntax::SmtLib2),
                VampireArg::ShowNew(true),
                VampireArg::Avatar(false),
            ],
            &smt,
        )?;

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
        if cfg!(debug_assertions) {
            let str = tmp
                .iter()
                .flatten()
                .map(|t| format!("{:}", t))
                .join(", ");
            debug!("instances found ({:?}):\n\t[{:}]", tmp.len(), str)
        }
        pbl.extra_instances.extend(
            tmp.into_iter()
                .flatten()
                .map(|t| t.translate_vars(max_var_no_instances).into()),
        )
    }

    Err(anyhow!("Ran out of tries"))
}
