// #![feature(box_syntax)]
// #![feature(box_patterns)]

use std::{env, fs::read_to_string, path::Path};

use automator::{formula::env::Environement, parser::parse_protocol, smt::writer::problem_to_smt};

extern crate pest_derive;

extern crate paste;

fn main() {
    let args: Vec<String> = env::args().collect();
    let tmp =
        "/Users/simon/Documents/Work/TU-Wien/SecPriv/PhD/ccsa/automator/hash_lock.ptcl".to_owned();
    let path = Path::new(args.get(1).unwrap_or(&tmp));

    let p = match parse_protocol(&read_to_string(path).expect("file not found")) {
        Ok(p) => p,
        Err(e) => {
            panic!("{}", e)
        }
    };
    // println!("{:?}", p)
    let smt = problem_to_smt(&Environement::default(), p);

    for s in smt {
        println!("{}", s);
    }
}
