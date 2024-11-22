use std::ffi::OsString;

use crate::{
    container::ScopedContainer,
    environement::environement::Environement,
    formula::{function::builtin::BUILT_IN_FUNCTIONS, sort::builtins::BUILT_IN_SORTS},
    smt::SmtFile,
};
use clap::Parser;
use log::trace;
use utils::from_with::FromWith;

use crate::{
    cli::Args,
    init_logger, parse_pbl_from_ast,
    parser::{self, ast::ASTList},
};

#[test]
fn miri() {
    init_logger();
    ScopedContainer::scoped(|container| {
        trace!("running");
        let env = Environement::from_with(&Args::parse_from::<_, OsString>([]), &*container);
        let ast = ASTList::try_from(TEST_FILE).unwrap();

        let pbl = parse_pbl_from_ast(
            container,
            BUILT_IN_SORTS.iter().cloned(),
            BUILT_IN_FUNCTIONS.iter().cloned(),
            parser::USED_KEYWORDS.iter().map(|s| s.to_string()),
            ast,
            env.are_lemmas_ignored(),
            true,
        )
        .expect("parsing error:");
        println!(
            "\n\n\n\n{}",
            SmtFile::from_general_file(&env, pbl.into_general_file(&env)).as_diplay(&env)
        )
    })
}
const TEST_FILE: &str = include_str!("../../../../tests/basic-hash-1.ptcl");
