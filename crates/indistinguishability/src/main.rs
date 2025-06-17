use indistinguishability::{
    init_logger,
    problem::{self, test::basic_hash::mk_pblm},
    rules::prf::test::basic_hash::mk_prf_rule,
};

pub fn main() {
    init_logger();
    let (mut pbl, funs) = mk_pblm();
    mk_prf_rule(&mut pbl, &funs);

    assert!(pbl.run(0, 1))
}
