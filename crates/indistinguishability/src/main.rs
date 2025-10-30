use std::fs::File;
use std::io::{self, Read};

use clap::Parser;
use indistinguishability::{Configuration, init_engine, init_logger};


static CV_PRELUDE: &str = include_str!("./input/prelude.scm");
pub fn main() {
    init_logger();
    let config = Configuration::parse();

    let pgrm = match &config.file {
        Some(f) => ::std::fs::read_to_string(f).unwrap(),
        None => {
            let mut pgrm = String::new();
            io::stdin()
                .read_to_string(&mut pgrm)
                .expect("Failed to read from stdin");
            pgrm
        }
    };

    // let res = init_engine().run(pgrm).unwrap();
    let mut engine = init_engine(config);
    match engine.run(pgrm.clone()) {
        Err(e) => {
            eprintln!("{}", e.emit_result_to_string("prelude", CV_PRELUDE));
            eprintln!("{}", e.emit_result_to_string("stdin", &pgrm));
            if let Some(err) = engine.raise_error_to_string(e) {
                panic!("{err}")
            } else {
                eprintln!("couldn't get a nice error");
                panic!()
            }
        }
        Ok(res) => {
            for r in res {
                println!("{r}")
            }
        }
    }
}
