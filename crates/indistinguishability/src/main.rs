use std::{fmt::Display, time::Duration};

use egg::{EGraph, FromOp, Id, Language, Runner, Symbol, SymbolLang};
use indistinguishability::{and_simpl_rewrite, MAnalysis, Program};
use utils::impossible::Impossible;

pub fn main() {
    init_logger();
    let mut pbl: Program<SymbolLang, () /* MAnalysis<_> */> =
        include_str!("../tests/test").parse().unwrap();
    pbl.set_explainations(true);
    // pbl.add_eq_rule(and_simpl_rewrite());
    pbl.config.time_limit = Duration::from_secs_f32(30.0);
    pbl.config.node_limit = 100000;
    pbl.config.iter_limit = 300;
    pbl.config.trace_prolog = true;

    // pbl.egraph_mut().analysis.weight_map = ["unfold", "exists$1", "exists$2"]
    //     .into_iter()
    //     .map(|s| (s.into(), (1, 0).into()))
    //     .collect();

    let r = pbl.run_expr("goal".parse().unwrap(), 7);
    pbl.egraph().dot().run_dot(&["-Kfdp", "-Tpdf", "-o", "/tmp/graph.pdf"]);
    // pbl.egraph().dot().to_dot("/tmp/dot.dot").unwrap();

    println!("{r}")
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
            } else {
                Ok(())
            }
        })
        .parse_default_env()
        .init();
}
