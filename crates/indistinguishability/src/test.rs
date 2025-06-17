pub mod basic_hash {
    use crate::{
        init_logger, problem::test::basic_hash::mk_pblm, rules::prf::test::basic_hash::mk_prf_rule,
    };

    #[test]
    fn run() {
        init_logger();
        let (mut pbl, funs) = mk_pblm();
        mk_prf_rule(&mut pbl, &funs);

        assert!(pbl.run(0, 1))
    }
}
