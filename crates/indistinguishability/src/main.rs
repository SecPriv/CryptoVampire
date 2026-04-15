//! The main executable for the indistinguishability analysis tool.
//! This module handles command-line argument parsing, initialization,
//! and execution of the analysis engine.

use std::io::{self, Read};

use clap::Parser;
use indistinguishability::{Commands, Configuration, init_engine, init_logger};

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
                engine.raise_error(e);
            }
        }
    }
}
