use std::fmt::Display;

use egg::{EGraph, FromOp, Id, Language, Runner, Symbol, SymbolLang};
use indistinguishability::Program;
use utils::impossible::Impossible;

pub fn main() {
    println!("hello world");
    let mut pbl: Program<SymbolLang, ()> = include_str!("../tests/test.pl").parse().unwrap();
    let r = pbl.run_expr("goal".parse().unwrap());
    print!("{r}")
}
