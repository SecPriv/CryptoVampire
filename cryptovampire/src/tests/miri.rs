use std::ffi::OsString;

use clap::Parser;
use cryptovampire_lib::{
    container::ScopedContainer,
    environement::environement::Environement,
    formula::{function::builtin::BUILT_IN_FUNCTIONS, sort::builtins::BUILT_IN_SORTS},
    smt::SmtFile,
};
use utils::from_with::FromWith;

use crate::{cli::Args, parser, problem_try_from_str};

#[test]
fn miri() {
    ScopedContainer::scoped(|container| {
        let env = Environement::from_with(&Args::parse_from::<_, OsString>([]), &*container);

        let pbl = problem_try_from_str(
            container,
            BUILT_IN_SORTS.iter().cloned(),
            BUILT_IN_FUNCTIONS.iter().cloned(),
            parser::USED_KEYWORDS.iter().map(|s| s.to_string()),
            &TEST_FILE,
            env.are_lemmas_ignored(),
        )
        .expect("parsing error:");
        println!(
            "\n\n\n\n{}",
            SmtFile::from_general_file(&env, pbl.into_general_file(&env)).as_diplay(&env)
        )
    })
}
const TEST_FILE: &'static str = include_str!("../../../test/basic-hash-1.ptcl");
