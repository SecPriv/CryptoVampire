use std::fmt::Display;

use clap::ValueEnum;
use static_init::dynamic;
use steel_derive::Steel;

use crate::terms::BUILTINS;

#[dynamic]
static CV_PRELUDE: String = {
    let mut mkdefintions: String = "\n".into();

    for f in BUILTINS {
        let name = &f.name;
        let old_name = format!("__pre_{}", f.name);
        mkdefintions += &format!("(define {name} (lift-fun {old_name}))\n");
    }

    include_str!("../../assets/preludes/v1.scm").replace("@@@DEFINITIONS@@@", &mkdefintions)
};
