use converters::convert_squirrel_dump;
use cryptovampire_lib::{
    container::{self, ScopedContainer},
    environement::environement::Environement,
    formula::{function::builtin::BUILT_IN_FUNCTIONS, sort::builtins::BUILT_IN_SORTS},
    problem::PblIterator,
};
use itertools::Either;
use json::SquirrelDump;
use utils::string_ref::StrRef;

use crate::{auto_run, parse_pbl_from_ast, parser};

mod converters;
pub(crate) mod json;

// FIXME: finish
pub fn run_from_json(str: &str) -> anyhow::Result<Vec<String>> {
    let dump: SquirrelDump = serde_json::from_str(str)?;
    convert_squirrel_dump(dump)?
        .into_iter()
        .map(|ast| {
            ScopedContainer::scoped(|container| {
                let pbl = parse_pbl_from_ast(
                    container,
                    BUILT_IN_SORTS.iter().cloned(),
                    BUILT_IN_FUNCTIONS.iter().cloned(),
                    parser::USED_KEYWORDS.iter().map(|s| s.to_string()),
                    ast,
                    true,
                )?;
                let pbls = PblIterator::new(pbl, false);

                let env: Environement = todo!();
                let runners = env.solver_configuration().clone().try_into()?;
                auto_run(&env, pbls, &runners, 5, None)
            })
        })
        .flat_map(|r| match r {
            Ok(v) => Either::Left(v.into_iter().map(Ok)),
            Err(e) => Either::Right([Err(e)].into_iter()),
        })
        .collect()
}


trait Sanitizer {
    fn sanitize<'a>(&self, str:&StrRef<'a>) -> StrRef<'a>;
}