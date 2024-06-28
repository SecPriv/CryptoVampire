#![allow(dead_code)]

#[cfg(test)]
mod tests;

use std::{
    fs::{self, read_to_string, File},
    io::{self, BufWriter, Read},
    num::NonZeroU32,
    path::{Path, PathBuf},
};

use crate::cli::Args;
use anyhow::{bail, ensure, Context};
use clap::Parser;
use cryptovampire_lib::{
    container::ScopedContainer,
    environement::environement::{AutomatedVampire, Environement},
    formula::{
        function::{builtin::BUILT_IN_FUNCTIONS, Function},
        sort::{builtins::BUILT_IN_SORTS, Sort},
    },
    problem::{PblIterator, Problem},
    runner::{VampireArg, VampireExec, VampireOutput},
    smt::{SmtFile, SMT_FILE_EXTENSION},
};
use itertools::Either;
use log::{log_enabled, trace};
use std::io::Write;
use utils::{
    from_with::FromWith,
    implvec,
    traits::{MyWriteTo, NicerError},
};
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

        let with_lemmas = env.are_lemmas_ignored() && args.lemmas;

        let pblsiter = PblIterator::new(pbl, with_lemmas);

        if let Some(av) = env.get_automated_vampire() {
            let out = auto_run(&env, pblsiter, av)?.pop().with_context(|| "empty output, nothing ran?")?;
            match out {
                VampireOutput::Unsat(proof) => println!("{proof}"),
                VampireOutput::TimeOut(fail) => bail!("last one timed out and this wasn't caught somehow:\n{fail}"),
            };
        } else if args.lemmas {
            run_to_dir(&env, pblsiter, &args.output_location)?;
        } else {
            run_to_file(&env, pblsiter, &args.output_location)?;
        }
        Ok(())

        // {
        //     if args.lemmas {
        //         assert!(
        //             !args.auto_retry,
        //             "Can't auto run vampire with lemma ativated"
        //         );
        //         assert!(
        //             !args.output_location.is_file(),
        //             "the oupput is a file, it should be a directory"
        //         );

        //         fs::create_dir_all(&args.output_location).expect("couldn't create dir");

        //         let mut i = 0;
        //         // for (i, smt) in smts.enumerate() {
        //         //     let path = args.output_location.join(Path::new(&format!("{}.smt", i)));
        //         //     write_to_file(&path, smt);
        //         // }

        //         let mut pbliter = PblIterator::from(pbl);

        //         while let Some(pbl) = pbliter.next() {
        //             let path = args.output_location.join(Path::new(&format!("{}.smt", i)));

        //             write_to_file(
        //                 &path,
        //                 SmtFile::from_general_file(&env, pbl.into_general_file(&env))
        //                     .as_diplay(&env),
        //             );

        //             i += 1;
        //         }
        //     } else if let Some(AutomatedVampire {
        //         location,
        //         num_retry,
        //         exec_time,
        //         ..
        //     }) = env.get_automated_vampire()
        //     {
        //         let vampire = VampireExec {
        //             location: location.to_owned(),
        //             extra_args: vec![VampireArg::TimeLimit(*exec_time)],
        //         };
        //         let result = run_multiple_time(*num_retry, &vampire, &env, &mut pbl).unwrap();
        //         let mut bw = BufWriter::new(io::stdout());
        //         if log_enabled!(log::Level::Debug) {
        //             write!(&mut bw, "{result}").unwrap();
        //         } else {
        //             for l in result.lines() {
        //                 if l.starts_with("[SA] new:") {
        //                     continue;
        //                 } else {
        //                     writeln!(&mut bw, "{l}").unwrap();
        //                 }
        //             }
        //         }
        //     } else {
        //         assert!(!args.output_location.is_dir());
        //         let smt = SmtFile::from_general_file(&env, pbl.into_general_file(&env));
        //         write_to_file(&args.output_location, smt.as_diplay(&env));
        //     }
        // }
    })
}

/// automatically run all the problems in `pbls` using `vampire`, retrying as many as `parms` requests it
pub fn auto_run<'bump>(
    env: &Environement<'bump>,
    mut pbls: PblIterator<'bump>,
    parms: &AutomatedVampire,
) -> anyhow::Result<Vec<VampireOutput>> {
    let exec = parms.to_vampire_exec();
    let ntimes = NonZeroU32::new(parms.num_retry);
    let save_to = parms.smt_debug.as_ref().map(|p| p.as_ref());

    pbls.map(&mut |pbl| exec.auto_run_vampire(env, pbl, ntimes, save_to))
        .flat_map(|r| match r {
            Ok(v) => Either::Left(v.into_iter().map(Ok)),
            Err(e) => Either::Right([Err(e)].into_iter()),
        })
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
        save_to_file(env, pbl, path.join(format!("{i:}{SMT_FILE_EXTENSION}")));
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

fn write_to_file(path: &PathBuf, smt: impl MyWriteTo) {
    let f = File::options()
        .write(true)
        .truncate(true)
        .create(true)
        .open(path)
        .unwrap_display();
    let mut bw = BufWriter::new(f);

    smt.write_to_io(&mut bw).unwrap()
}
