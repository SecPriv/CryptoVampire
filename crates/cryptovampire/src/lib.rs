#![recursion_limit = "256"]
#[allow(clippy::module_inception)]
pub mod cli;
pub mod container;
pub mod environement;
pub mod error;
pub mod formula;
pub mod location;
pub mod parser;
pub mod problem;
mod return_value;
pub mod runner;
pub mod smt;
pub mod squirrel;
pub mod subterm;

#[cfg(test)]
mod tests;

use std::fs::File;
use std::io::BufWriter;
use std::num::NonZeroU32;
use std::path::Path;

use error::BaseContext;
// reexports
pub use error::{Error, Result, Unit};
use log::trace;
use parser::Pstr;
use parser::ast::ASTList;
pub use parser::parse_pbl_from_ast;
pub use problem::step::INIT_STEP_NAME;
pub use return_value::Return;
use runner::RunnerResult;
use smt::SmtDisplay;
pub use subterm::kind::SubtermKind;
use utils::from_with::FromWith;
use utils::string_ref::StrRef;
use utils::traits::MyWriteTo;

// other imports
use crate::cli::Args;
use crate::container::ScopedContainer;
use crate::environement::environement::{Environement, SolverConfig};
use crate::formula::function::builtin::BUILT_IN_FUNCTIONS;
use crate::formula::sort::builtins::BUILT_IN_SORTS;
use crate::problem::{PblIterator, Problem};
use crate::runner::Runners;
use crate::smt::{SMT_FILE_EXTENSION, SmtFile};

mod cv_utils;
pub use cv_utils::FromEnv;

// start of the file

pub fn run_from_cv(args: Args, str: &str) -> crate::Result<Return> {
    trace!("running for cryptovampire file");
    let ast = ASTList::try_from(str)?;
    run_from_ast(&args, ast)
}

fn run_from_ast<'a, S>(args: &Args, ast: ASTList<'a, S>) -> crate::Result<Return>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    trace!("running from ast file");
    ScopedContainer::scoped(|container| {
        let env = Environement::from_with(args, &*container);

        let pbl = parse_pbl_from_ast(
            container,
            BUILT_IN_SORTS.iter().cloned(),
            BUILT_IN_FUNCTIONS.iter().cloned(),
            parser::USED_KEYWORDS.iter().map(|s| s.to_string()),
            ast,
            env.are_lemmas_ignored(),
            env.allow_shadowing(),
        )?;

        let with_lemmas = env.use_lemmas();

        let pblsiter = PblIterator::new(pbl, with_lemmas);

        if let Some(output_location) = args.get_output_location() {
            if env.use_lemmas() {
                run_to_dir(&env, pblsiter, output_location)?;
            } else {
                run_to_file(&env, pblsiter, output_location)?;
            };
            Ok(Return::ToFile(output_location.to_path_buf()))
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
            )?;
            if out.is_empty() {
                bail!("empty output, nothing ran?")
            }
            Ok(Return::AutoRun(out))
        }
    })
}

/// automatically run all the problems in `pbls` using `vampire`, retrying as many
/// as `parms` requests it
pub fn auto_run<'bump>(
    env: &Environement<'bump>,
    mut pbls: PblIterator<'bump>,
    runners: &Runners,
    num_retry: u32,
    smt_debug: Option<&Path>,
) -> crate::Result<Vec<RunnerResult>> {
    let ntimes = NonZeroU32::new(num_retry);
    let save_to = smt_debug;

    pbls.map(&mut |pbl| runners.clone().autorun(env, pbl, ntimes, save_to))
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
) -> crate::Result<()> {
    std::fs::create_dir_all(path)?;

    let mut i = 0;
    #[allow(clippy::map_collect_result_unit)]
    pbls.map(&mut |pbl| {
        save_to_file(env, pbl, path.join(format!("{i:}{SMT_FILE_EXTENSION}")))?;
        i += 1;
        Ok(())
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
) -> crate::Result<()> {
    if !path.exists() {
        std::fs::create_dir_all(path.parent().with_context((), || "already a root")?)?;
    }
    ensure!(
        (),
        pbls.assert_one(),
        "More than one problem queued, are you using lemmas?"
    )?;

    let npbl = pbls.next().with_context((), || "no problems are queued")?;
    save_to_file(env, npbl, path)?;
    debug_assert!(pbls.next().is_none());
    Ok(())
}

/// Save `pbl` to `path`, return an error if the file doesn't exists
fn save_to_file<'bump>(
    env: &Environement<'bump>,
    pbl: &mut Problem<'bump>,
    path: impl AsRef<Path>,
) -> crate::Result<()> {
    let file = File::options()
        .write(true) // write mode
        .truncate(true) // overwrite
        .create(true) // create if necessary
        .open(path)?;
    SmtFile::with_env(env, pbl.into_general_file(env)) // gen smt
        .as_display(env)
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
