#[cfg(test)]
mod tests;

use std::{fs::File, io::BufWriter, num::NonZeroU32, path::Path};

use crate::cli::Args;
use anyhow::{ensure, Context};

use cryptovampire_lib::{
    container::ScopedContainer,
    environement::environement::{Environement, SolverConfig},
    formula::{
        function::{builtin::BUILT_IN_FUNCTIONS, Function},
        sort::{builtins::BUILT_IN_SORTS, Sort},
    },
    problem::{PblIterator, Problem},
    runner::Runners,
    smt::{SmtFile, SMT_FILE_EXTENSION},
};

use utils::{from_with::FromWith, implvec, traits::MyWriteTo};
pub mod cli;
pub mod parser;

/// parse a [Problem] object form a string
pub fn problem_try_from_str<'a, 'bump>(
    container: &'bump ScopedContainer<'bump>,
    sort_hash: implvec!(Sort<'bump>),
    function_hash: implvec!(Function<'bump>),
    extra_names: implvec!(String),
    str: &'a str,
    ignore_lemmas: bool,
) -> anyhow::Result<Problem<'bump>> {
    parser::parse_str(
        container,
        sort_hash,
        function_hash,
        extra_names,
        str,
        ignore_lemmas,
    )
}

pub fn run(args: Args, str: &str) -> anyhow::Result<()> {
    ScopedContainer::scoped(|container| {
        let env = Environement::from_with(&args, &*container);

        let pbl = problem_try_from_str(
            container,
            BUILT_IN_SORTS.iter().cloned(),
            BUILT_IN_FUNCTIONS.iter().cloned(),
            parser::USED_KEYWORDS.iter().map(|s| s.to_string()),
            &str,
            env.are_lemmas_ignored(),
        )?;

        let with_lemmas = env.use_lemmas();

        let pblsiter = PblIterator::new(pbl, with_lemmas);

        if let Some(output_location) = args.get_output_location() {
            if env.use_lemmas() {
                run_to_dir(&env, pblsiter, output_location)?;
            } else {
                run_to_file(&env, pblsiter, output_location)?;
            }
        } else {
            let SolverConfig {
                num_of_retry,
                smt_debug,
                ..
            } = env.solver_configuration();
            let runner = env.solver_configuration().clone().try_into()?;
            let out = auto_run(
                &env,
                pblsiter,
                &runner,
                *num_of_retry,
                smt_debug.as_ref().map(|p| p.as_path()),
            )?
            .pop()
            .with_context(|| "empty output, nothing ran?")?;
            println!("{out}");
        }
        Ok(())
    })
}

/// automatically run all the problems in `pbls` using `vampire`, retrying as many as `parms` requests it
pub fn auto_run<'bump>(
    env: &Environement<'bump>,
    mut pbls: PblIterator<'bump>,
    runners: &Runners,
    num_retry: u32,
    smt_debug: Option<&Path>,
) -> anyhow::Result<Vec<String>> {
    let ntimes = NonZeroU32::new(num_retry);
    let save_to = smt_debug;

    pbls.map(&mut |pbl| runners.autorun(env, pbl, ntimes, save_to))
        .collect()
}

/// run multiple problem to smt files saved in the `path` directory
///
/// ## error
/// - if `path` isn't a directory (or can't be created)
/// - any io error
/// - any generation error
pub fn run_to_dir<'bump>(
    env: &Environement<'bump>,
    mut pbls: PblIterator<'bump>,
    path: &Path,
) -> anyhow::Result<()> {
    std::fs::create_dir_all(path)?;

    let mut i = 0;
    pbls.map(&mut |pbl| {
        save_to_file(env, pbl, path.join(format!("{i:}{SMT_FILE_EXTENSION}")))?;
        Ok(i += 1)
    })
    .collect()
}

/// run multiple problem to smt files saved in the `path` directory
///
/// ## error
/// - if `path` isn't a file (or can't be created)
/// - any io error
/// - any generation error
/// - `pbl` can't prove it has exactly one problem stored
pub fn run_to_file<'bump>(
    env: &Environement<'bump>,
    mut pbls: PblIterator<'bump>,
    path: &Path,
) -> anyhow::Result<()> {
    if !path.exists() {
        std::fs::create_dir_all(path.parent().with_context(|| "already a root")?)?;
    }
    ensure!(
        pbls.assert_one(),
        "More than one problem queued, are you using lemmas?"
    );

    let mut npbl = pbls.next().with_context(|| "no problems are queued")?;
    save_to_file(env, &mut npbl, path)?;
    debug_assert!(pbls.next().is_none());
    Ok(())
}

/// Save `pbl` to `path`, return an error if the file doesn't exists
fn save_to_file<'bump>(
    env: &Environement<'bump>,
    pbl: &mut Problem<'bump>,
    path: impl AsRef<Path>,
) -> anyhow::Result<()> {
    let file = File::options()
        .write(true) // write mode
        .truncate(true) // overwrite
        .create(true) // create if necessary
        .open(path)?;
    SmtFile::from_general_file(env, pbl.into_general_file(&env)) // gen smt
        .as_diplay(env)
        .write_to_io(&mut BufWriter::new(file))?;
    Ok(())
}

use std::io::Write;
pub fn init_logger() {
    env_logger::Builder::new()
        .format(|buf, record| {
            let str = record.args().to_string().replace("\n", "\n\t");
            writeln!(
                buf,
                "[{}] in {}:{}\n\t{}",
                record.level(),
                record.file().unwrap_or("unknown"),
                record.line().unwrap_or(0),
                str
            )
        })
        .parse_default_env()
        .init();
}
