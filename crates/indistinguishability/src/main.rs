use std::io::{self, Read};

use indistinguishability::{init_engine, init_logger};

static CV_PRELUDE: &str = include_str!("./input/prelude.scm");
pub fn main() {
    init_logger();

    let mut pgrm = String::new();
    io::stdin()
        .read_to_string(&mut pgrm)
        .expect("Failed to read from stdin");

    // let res = init_engine().run(pgrm).unwrap();
    let mut engine = init_engine();
    match engine.run(pgrm.clone()) {
        Err(e) => {
            eprintln!("{}", e.emit_result_to_string("prelude", CV_PRELUDE));
            eprintln!("{}", e.emit_result_to_string("stdin", &pgrm));
            if let Some(err) = engine.raise_error_to_string(e) {
                panic!("{err}")
            } else {
                eprintln!("couldn't get a nice error");
                panic!()
            }
        }
        Ok(res) => {
            for r in res {
                println!("{r}")
            }
        }
    }
}
