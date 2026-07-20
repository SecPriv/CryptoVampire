//! The main executable for the indistinguishability analysis tool.
//! This module handles command-line argument parsing, initialization,
//! and execution of the analysis engine.

use std::io::{self, Read};

use clap::Parser;
use indistinguishability::{Configuration, RunningMode, init_engine, init_logger};
use steel::rerrs::ErrorKind;

// static CV_PRELUDE: &str = include_str!("./input/prelude.scm");
pub fn main() {
    let config = Configuration::from_cli();
    init_logger();
    let mode = config.get_mode();
    let mut engine = init_engine(config);

    match mode {
        RunningMode::Repl => {
            steel_repl::run_repl(engine).unwrap();
        }
        x => {
            let pgrm = match x {
                RunningMode::File(file) => ::std::fs::read_to_string(file).unwrap(),
                RunningMode::Stdin => {
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
