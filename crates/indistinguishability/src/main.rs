//! The main executable for the indistinguishability analysis tool.
//! This module handles command-line argument parsing, initialization,
//! and execution of the analysis engine.

use std::io::{self, Read};

use clap::Parser;
use indistinguishability::{Commands, Configuration, init_engine, init_logger};

// static CV_PRELUDE: &str = include_str!("./input/prelude.scm");
pub fn main() {
    let config = Configuration::parse();
    init_logger();
    let mode = config.command.clone().unwrap_or_default();
    let mut engine = init_engine(config);

    match mode {
        Commands::Repl => {
            steel_repl::run_repl(engine).unwrap();
        }
        x => {
            let pgrm = match x {
                Commands::File { file } => {
                    engine.add_search_directory(file.parent().unwrap().to_path_buf());
                    ::std::fs::read_to_string(file).unwrap()
                }
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
                if let Some(err) = engine.raise_error_to_string(e.clone()) {
                    panic!("{err}")
                } else {
                    eprintln!("{}", e.emit_result_to_string("stdin", &pgrm));
                    panic!("Steel crashed and we could not get a nice error out of it...");
                }
            }
        }
    }

    // let pgrm = match &config.file {
    //     Some(f) => ::std::fs::read_to_string(f).unwrap(),
    //     None => {
    //         let mut pgrm = String::new();
    //         io::stdin()
    //             .read_to_string(&mut pgrm)
    //             .expect("Failed to read from stdin");
    //         pgrm
    //     }
    // };

    // // let res = init_engine().run(pgrm).unwrap();

    // match engine.run(pgrm.clone()) {
    //     Err(e) => {
    //         // eprintln!("{}", e.emit_result_to_string("prelude", CV_PRELUDE));
    //         if let Some(err) = engine.raise_error_to_string(e.clone()) {
    //             panic!("{err}")
    //         } else {
    //             eprintln!("{}", e.emit_result_to_string("stdin", &pgrm));
    //             panic!("Steel crashed and we could get a nice error out of it...");
    //         }
    //     }
    //     Ok(_) => {
    //         // for r in res {
    //         //     println!("{r}")
    //         // }
    //     }
    // }
}
