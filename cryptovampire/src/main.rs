use std::{
    fs::{self, read_to_string, File},
    io::{self, BufWriter, Read},
    path::{Path, PathBuf},
};

use clap::Parser;
use cryptovampire::{cli::Args, parser, problem_try_from_str, run};
use cryptovampire_lib::{
    container::ScopedContainer,
    environement::environement::{AutomatedVampire, Environement},
    formula::{function::builtin::BUILT_IN_FUNCTIONS, sort::builtins::BUILT_IN_SORTS},
    problem::PblIterator,
    smt::SmtFile,
};
use log::{log_enabled, trace};
use std::io::Write;
use utils::{
    from_with::FromWith,
    traits::{MyWriteTo, NicerError},
};

fn main() {
    let args = Args::parse();

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

    trace!("start");
    trace!("read input...");
    let str = {
        if let Some(file) = &args.file {
            read_to_string(file).unwrap_or_else(|_| {
                panic!(
                    "file \"{}\" not found",
                    file.to_str().unwrap_or("[non-unicode file name]")
                )
            })
        } else {
            let mut buf = String::new();
            Read::read_to_string(&mut io::stdin(), &mut buf).expect("unable to read stdin");
            buf
        }
    };
    run(args, &str).unwrap();
    trace!("done")
}
