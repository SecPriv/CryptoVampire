use std::io::{self, Read};

use indistinguishability::{
    init_engine, init_logger,
    problem::{self, test::basic_hash::mk_pblm},
    rules::prf::test::basic_hash::mk_prf_rule,
};
use steel::steel_vm::{builtin::BuiltInModule, engine::Engine};

static CV_PRELUDE : &str = include_str!("./input/prelude.scm");
pub fn main() {
    init_logger();

    let mut pgrm = String::new();
    io::stdin()
        .read_to_string(&mut pgrm)
        .expect("Failed to read from stdin");

    // let res = init_engine().run(pgrm).unwrap();
    match init_engine().run(pgrm.clone()) {
        Err(e) =>  eprintln!("{}", e.emit_result_to_string("stdin", CV_PRELUDE)),
        Ok(res) => {
            for r in res {
                println!("{r}")
            }
        }
    }
}
