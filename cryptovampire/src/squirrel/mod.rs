use std::io::BufReader;

use converters::convert_squirrel_dump;
use json::CryptoVampireCall;
use log::{debug, trace};
use utils::string_ref::StrRef;

use crate::{cli::Args, run_from_ast};

mod converters;
pub(crate) mod json;

pub fn run_from_json(mut args: Args, str: &str) -> anyhow::Result<()> {
    debug!("running from json");
    assert!(args.input_format.is_squirrel_json());

    debug!("parsing json");
    let dump = {
        let tmp: CryptoVampireCall = serde_json::from_str(str)?;
        tmp.context
    };
    trace!("parsing successful");

    trace!("converting to ast");
    convert_squirrel_dump(dump)?
        .into_iter()
        .enumerate()
        .map(|(i, ast)| {
            if cfg!(debug_assertions) {
                match std::env::var("CRYTPOVAMPIRE_DUMP") {
                    Ok(f) => std::fs::write(f, ast.to_string()).unwrap(),
                    Err(std::env::VarError::NotPresent) => (),
                    x => {
                        x.unwrap();
                    }
                }
                trace!("runnig the {i}th problem with ast:\n\t{ast}");
            }

            match args.get_mut_output_location() {
                None => (),
                Some(location) => *location = location.join(&format!("{i}")),
            }

            run_from_ast(&args, ast)
        })
        .collect()
}

trait Sanitizer {
    fn sanitize<'a>(&self, str: &StrRef<'a>) -> StrRef<'a>;
}
