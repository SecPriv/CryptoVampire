pub fn main() {
    use test::*;
    basic_hash();
}

mod test {
    use std::{
        fs::{File, read_to_string},
        u128,
    };

    use egg::{EGraph, Runner, SymbolLang};
    use golgge::Program;

    use indistinguishability::{init_logger, rules::VampireRule};
    use std::env;

    static TEST_DIR: &str = "tests";

    #[test]
    fn test() {
        let pbl: Program<SymbolLang, () /* MAnalysis<_> */> =
            read_to_string(format!("{TEST_DIR}/basic_hash/main"))
                .unwrap()
                .parse()
                .unwrap();
        // include_str!(concat!()).parse().unwrap();
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

    #[test]
    fn test_basic_hash() {
        basic_hash();
    }

    /// Runs the `basic_hash` example
    pub fn basic_hash() {
        let itern: u128 = u128::MAX;

        let main = read_to_string(format!("{TEST_DIR}/basic_hash/main")).unwrap();
        let prelude = read_to_string(format!("{TEST_DIR}/basic_hash/prelude.smt")).unwrap();

        init_logger();
        let mut pbl: Program<SymbolLang, () /* MAnalysis<_> */> = main.parse().unwrap();
        pbl.set_explainations(false);
        pbl.set_memo(itern == u128::MAX);
        pbl.add_rule(VampireRule::new(prelude.into(), 0));
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
}
