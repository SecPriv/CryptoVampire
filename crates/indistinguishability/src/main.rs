use std::{fmt::Display, time::Duration};

use egg::{EGraph, FromOp, Id, Language, Runner, Symbol, SymbolLang};
use indistinguishability::{and_simpl_rewrite, Program};
use utils::impossible::Impossible;

pub fn main() {
    init_logger();
    let mut pbl: Program<SymbolLang, ()> = include_str!("../tests/test.pl").parse().unwrap();
    pbl.set_explainations(true);
    pbl.add_eq_rule(and_simpl_rewrite());
    pbl.runner_config.time_limit = Duration::from_secs_f32(10.0);
    let r = pbl.run_expr("goal".parse().unwrap());
    pbl.egraph().dot().to_pdf("/tmp/egraph.pdf");


    print!("{r}")
}

use std::io::Write;
fn init_logger() {
    env_logger::Builder::new()
        .format(|buf, record| {
            if record.file().map(|s| s.contains("egg")) != Some(true) {

            let str = record.args().to_string().replace("\n", "\n\t");
            writeln!(
                buf,
                "[{}] in {}:{}\n\t{}",
                record.level(),
                record.file().unwrap_or("unknown"),
                record.line().unwrap_or(0),
                str
            )
            } else {Ok(())}
        })
        .parse_default_env()
        .init();
}