// #![feature(box_syntax)]
// #![feature(box_patterns)]

use std::{env, fs::read_to_string, path::Path};

use automator::parser::parse_protocol;

extern crate pest_derive;

extern crate paste;

fn main() {
    let args: Vec<String> = env::args().collect();
    let path = Path::new(&args[1]);

    let p = match parse_protocol(&read_to_string(path).expect("file not found")) {
        Ok(p) => p,
        Err(e) => {
            panic!("{}", e)
        }
    };
    println!("{:?}", p)
}
