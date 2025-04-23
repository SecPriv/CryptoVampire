use std::fmt::Display;

use egg::{EGraph, FromOp, Id, Language, Runner, Symbol, SymbolLang};
use indistinguishability::{and_simpl_rewrite, Program};
use utils::impossible::Impossible;

pub fn main() {
    println!("hello world");
    let mut pbl: Program<SymbolLang, ()> = include_str!("../tests/test.pl").parse().unwrap();
    pbl.set_explainations(true);
    pbl.add_eq_rule(and_simpl_rewrite());
    // pbl.runner_config.node_limit = 3000;
    let r = pbl.run_expr("goal".parse().unwrap());
    pbl.egraph().dot().to_pdf("/tmp/egraph.pdf");
    print!("{r}")
}
