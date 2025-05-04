use std::{fmt::Display, time::Duration, u128};

use egg::{EGraph, FromOp, Id, Language, Runner, Symbol, SymbolLang};
use indistinguishability::{and_simpl_rewrite, MAnalysis, Program, VampireRule};
use std::{env};
use utils::impossible::Impossible;

pub fn main() {
    let itern: u128 = {
        let mut args = env::args();
        args.next();
        args.next()
    }
    .map(|x| x.parse().unwrap())
    .unwrap_or(u128::MAX);

    init_logger();
    let mut pbl: Program<SymbolLang, () /* MAnalysis<_> */> =
        include_str!("../tests/test").parse().unwrap();
    pbl.set_explainations(false);
    pbl.set_memo(itern == u128::MAX);
    pbl.add_rule(VampireRule::new(include_str!("../tests/prelude.tptp"), 0));
    // pbl.add_eq_rule(and_simpl_rewrite());
    // pbl.config.time_limit = Duration::from_secs_f32(60.0);
    pbl.config.node_limit = 100000;
    // pbl.config.iter_limit = 300;
    pbl.config.trace_prolog = true;

    let r = pbl.run_expr("goal".parse().unwrap(), itern);
    println!("{r}");
    // pbl.egraph().dot().run_dot(&["-Ksfdp", "-Tpdf", "-o", "/tmp/graph.pdf"]);
    // pbl.egraph().dot().to_pdf("/tmp/graph.pdf");
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

#[cfg(test)]
mod test {
    use std::fs::File;

    use egg::{EGraph, Runner, SymbolLang};
    use indistinguishability::Program;

    #[test]
    fn test() {
        let mut pbl: Program<SymbolLang, () /* MAnalysis<_> */> =
            include_str!("../tests/test").parse().unwrap();
        let rules = pbl.eq_rules();

        let f = File::open("/tmp/graph.json").unwrap();
        let mut x = serde_json::Deserializer::from_reader(f);
        let egraph: EGraph<SymbolLang, ()> = serde::Deserialize::deserialize(&mut x).unwrap();

        let r: Runner<SymbolLang, ()> = Runner::new(()).with_egraph(egraph).run(rules);

        println!("1: {}", r.report());

        let egraph = r.egraph;
        let r: Runner<SymbolLang, ()> = Runner::new(()).with_egraph(egraph.clone()).run(rules);

        println!("2: {}", r.report());
    }
}
