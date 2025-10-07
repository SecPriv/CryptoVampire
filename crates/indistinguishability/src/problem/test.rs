pub mod basic_hash {
    use crate::Problem;
    use crate::protocol::test::basic_hash::{
        MFunction, insert_rf, insert_rs, insert_rw, insert_tag, populate_functions,
    };

    pub fn mk_pblm() -> (Problem, MFunction) {
        let mut pbl = Problem::builder().build();
        pbl.config.keep_smt_files = true;
        let funs = populate_functions(&mut pbl);
        // insert_init(&mut pbl, &funs);
        insert_tag(&mut pbl, &funs);
        insert_rs(&mut pbl, &funs);
        insert_rf(&mut pbl, &funs);
        insert_rw(&mut pbl, &funs);
        (pbl, funs)
    }

    #[cfg(test)]
    mod test {

        use egg::{EGraph, Runner};
        use itertools::Itertools;

        use crate::problem::test::basic_hash::mk_pblm;
        use crate::rules::mk_default_rewrites;
        use crate::terms::{HAPPENS, MACRO_INPUT, MACRO_MSG};
        use crate::{Lang, decl_fun, rexp};

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

            let rw = mk_default_rewrites(&pbl).collect_vec();
            let runner: Runner<Lang, ()> = Runner::new(());
            runner.with_egraph(egraph).run(&rw);
        }
    }
}
