use converters::convert_squirrel_dump;
use cryptovampire_lib::container::ScopedContainer;
use json::SquirrelDump;
use utils::string_ref::StrRef;

use crate::{cli::Args, run_from_ast};

mod converters;
pub(crate) mod json;

pub fn run_from_json(mut args: Args, str: &str) -> anyhow::Result<()> {
    assert!(args.input_format.is_squirrel_json());

    let dump: SquirrelDump = serde_json::from_str(str)?;
    convert_squirrel_dump(dump)?
        .into_iter()
        .enumerate()
        .map(|(i, ast)| {
            ScopedContainer::scoped(|container| {
                match args.get_mut_output_location() {
                    None => (),
                    Some(location) => *location = location.join(&format!("{i}")),
                }

                run_from_ast(&args, ast)
            })
        })
        .collect()
}

trait Sanitizer {
    fn sanitize<'a>(&self, str: &StrRef<'a>) -> StrRef<'a>;
}
