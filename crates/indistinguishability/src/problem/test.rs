use egg::{EGraph, RecExpr, Runner};
use itertools::Itertools;
use utils::implvec;

use crate::{Lang, Problem, rules::base_rules::mk_rewrites_rules};

pub mod basic_hash {
    use egg::{EGraph, Runner};
    use itertools::Itertools;

    use crate::{
        Lang, Problem, decl_fun,
        protocol::test::basic_hash::{
            MFunction, insert_init, insert_rf, insert_rs, insert_rw, insert_tag, populate_functions,
        },
        rexp,
        rules::base_rules::mk_rewrites_rules,
        terms::{HAPPENS, MACRO_INPUT, MACRO_MSG, formula_utils::convert_to_ground_rexp},
    };

    pub fn mk_pblm() -> (Problem, MFunction) {
        let mut pbl = Problem::base_empty();
        pbl.config.keep_smt_files = true;
        let funs = populate_functions(&mut pbl);
        insert_init(&mut pbl, &funs);
        insert_tag(&mut pbl, &funs);
        insert_rs(&mut pbl, &funs);
        insert_rf(&mut pbl, &funs);
        insert_rw(&mut pbl, &funs);
        (pbl, funs)
    }

    #[test]
    fn test_mk_pblm() {
        mk_pblm();
    }

    #[test]
    fn test_mk_egraph() {
        let mut pbl = mk_pblm().0;
        let i = decl_fun!(&mut pbl; "i": () -> Index);
        let j = decl_fun!(&mut pbl; "j": () -> Index);
        let p1 = pbl.protocols[0].name();
        let tag = pbl.function.get("tag").unwrap();

        let mut egraph = EGraph::new(());
        egraph.add_expr(&convert_to_ground_rexp(rexp!((MACRO_INPUT (tag i j) p1))).unwrap());
        egraph.add_expr(&convert_to_ground_rexp(rexp!((MACRO_MSG (tag i j) p1))).unwrap());
        egraph.add_expr(&convert_to_ground_rexp(rexp!((HAPPENS (tag i j)))).unwrap());
        egraph.rebuild();

        let rw = mk_rewrites_rules(&pbl).collect_vec();
        let runner: Runner<Lang, ()> = Runner::new(());
        runner.with_egraph(egraph).run(&rw);
    }
}
