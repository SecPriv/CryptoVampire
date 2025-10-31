use std::fmt::Display;

use converters::convert_squirrel_dump;
use itertools::Itertools;
use json::CryptoVampireCall;
use log::{debug, trace};
use utils::string_ref::StrRef;

use crate::cli::Args;
use crate::{Return, run_from_ast};

mod converters;
pub(crate) mod json;

pub fn run_from_json(mut args: Args, str: &str) -> crate::Result<Vec<Return>> {
    debug!("running from json");
    assert!(args.input_format.is_squirrel_json());

    debug!("parsing json");
    let dump = {
        let tmp: CryptoVampireCall<'_> = serde_json::from_str(str)?;
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
                Some(location) => *location = location.join(format!("{i}")),
            }
            run_from_ast(&args, ast)
        })
        .try_collect()
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum SanitizeKind {
    Variable,
    Function,
    Step,
    Macro,
    Cell,
    Name,
    Sort,
}

impl Display for SanitizeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            SanitizeKind::Variable => "var",
            SanitizeKind::Function | SanitizeKind::Macro => "fun",
            SanitizeKind::Step => "step",
            SanitizeKind::Cell => "cell",
            SanitizeKind::Name => "name",
            SanitizeKind::Sort => "sort",
        };
        write!(f, "{str}_")
    }
}

pub trait Sanitizable<'a> {
    fn to_str_ref(&self) -> StrRef<'a>;

    fn sanitize_kind(&self) -> SanitizeKind;

    fn sanitized<S: Sanitizer>(&self, sanitizer: &S) -> StrRef<'a>
    where
        Self: Sized,
    {
        sanitizer.sanitize(self)
    }
}

pub trait Sanitizer {
    fn sanitize<'a, S: Sanitizable<'a>>(&self, str: &S) -> StrRef<'a>;
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FakeSanitizable<'a> {
    pub str: StrRef<'a>,
    pub kind: SanitizeKind,
}
impl<'a> Sanitizable<'a> for FakeSanitizable<'a> {
    fn to_str_ref(&self) -> StrRef<'a> {
        self.str.clone()
    }

    fn sanitize_kind(&self) -> SanitizeKind {
        self.kind
    }
}
