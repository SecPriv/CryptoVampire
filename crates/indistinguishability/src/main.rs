//! The main executable for the indistinguishability analysis tool.
//! This module handles command-line argument parsing, initialization,
//! and execution of the analysis engine.

use std::io::{self, Read};

use clap::Parser;
use indistinguishability::{Commands, Configuration, init_engine, init_logger};
use steel::rerrs::ErrorKind;

// static CV_PRELUDE: &str = include_str!("./input/prelude.scm");
pub fn main() {
    let config = Configuration::from_cli();
    init_logger();
    let mode = config.command.clone().unwrap_or_default();
    let mut engine = init_engine(config);

    match mode {
        Commands::Repl => {
            steel_repl::run_repl(engine).unwrap();
        }
        x => {
            let pgrm = match x {
                Commands::File { file } => ::std::fs::read_to_string(file).unwrap(),
                Commands::Stdin => {
                    let mut pgrm = String::new();
                    io::stdin()
                        .read_to_string(&mut pgrm)
                        .expect("Failed to read from stdin");
                    pgrm
                }
                _ => unreachable!(),
            };

            if let Err(e) = engine.run(pgrm.clone()) {
                let err = to_error_code(&e.kind());
                engine.raise_error(e);
                std::process::exit(err)
            }
        }
    }
}

fn to_error_code(kind: &ErrorKind) -> i32 {
    use ErrorKind::*;
    match kind {
        ArityMismatch => 1,
        FreeIdentifier => 2,
        TypeMismatch => 3,
        UnexpectedToken => 4,
        ContractViolation => 5,
        BadSyntax => 6,
        ConversionError => 7,
        Io => 8,
        Parse => 9,
        Infallible => 10,
        Generic => 11,
    }
}
