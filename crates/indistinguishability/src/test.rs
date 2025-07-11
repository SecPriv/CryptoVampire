pub mod basic_hash {
    use crate::init_logger;
    use crate::problem::PRule;
    use crate::problem::test::basic_hash::mk_pblm;
    use crate::rules::prf_test::basic_hash::mk_prf_rule;

    #[test]
    fn run() {
        init_logger();
        let (mut pbl, funs) = mk_pblm();
        let prf = mk_prf_rule(&mut pbl, &funs);
        pbl.extra_rules_mut().push(prf.into_mrc());

        assert!(pbl.run(0, 1))
    }
}
