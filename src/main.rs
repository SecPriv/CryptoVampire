// #![feature(box_syntax)]
// #![feature(box_patterns)]

use automator::parser::parse_protocol;

#[macro_use]
extern crate pest_derive;

#[macro_use]
extern crate paste;

fn main() {
    println!("Hello, world!");

    let t = "let ceci_Est_un_tests -> bool;

    step reader() {true && &(i) {false(i) || true}}{empty}";

    parse_protocol(t);
}
