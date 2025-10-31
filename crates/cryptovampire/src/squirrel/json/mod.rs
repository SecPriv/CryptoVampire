use std::fmt::Display;

use log::trace;
use serde::{Deserialize, Serialize};

/// Forbiden characters in cv's input
const FORBIDDEN: &str = ";$#";

pub const DUMMY_VAR: &str = "$dummy";

macro_rules! new_name {
    ($name:ident: $kind:ident) => {
        #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
        pub struct $name<'a>(#[serde(borrow)] pub $crate::squirrel::json::Path<'a>);

        impl<'a> $crate::squirrel::Sanitizable<'a> for $name<'a> {
            fn to_str_ref(&self) -> utils::string_ref::StrRef<'a> {
                self.0.to_str_ref()
            }

            fn sanitize_kind(&self) -> $crate::squirrel::SanitizeKind {
                $crate::squirrel::SanitizeKind::$kind
            }
        }

        impl<'a> std::borrow::Borrow<$crate::squirrel::json::path::Path<'a>> for $name<'a> {
            fn borrow(&self) -> &$crate::squirrel::json::path::Path<'a> {
                &self.0
            }
        }


        paste::paste! {
            #[allow(dead_code)]
            #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
            pub struct [<$name Ref>]<'a, 'b>(pub &'b $crate::squirrel::json::Path<'a>);

            impl<'a, 'b> $crate::squirrel::Sanitizable<'a> for [<$name Ref>]<'a, 'b> {
                fn to_str_ref(&self) -> utils::string_ref::StrRef<'a> {
                    self.0.to_str_ref()
                }

                fn sanitize_kind(&self) -> $crate::squirrel::SanitizeKind {
                    $crate::squirrel::SanitizeKind::$kind
                }
            }

            impl<'a, 'b> std::borrow::Borrow<$crate::squirrel::json::path::Path<'a>> for [<$name Ref>]<'a, 'b> {
                fn borrow(&self) -> &$crate::squirrel::json::path::Path<'a> {
                    self.0
                }
            }

            impl<'a, 'b> hashbrown::Equivalent<$name<'a>> for [<$name Ref>]<'a, 'b> {
                fn equivalent(&self, key: &$name<'a>) -> bool {
                    self.0 == &key.0
                }
            }

            #[allow(dead_code)]
            impl<'a> $name<'a> {
                pub fn as_ref<'b>(&'b self) -> [<$name Ref>]<'a, 'b> {
                    [<$name Ref>](&self.0)
                }
            }
        }
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct CryptoVampireStrValidator;

impl utils::string_ref::Validator for CryptoVampireStrValidator {
    #[inline]
    fn validate(&self, str: &str) -> bool {
        let res = str == DUMMY_VAR || !str.chars().any(|x| FORBIDDEN.contains(x));

        if cfg!(debug_assertions) && !res {
            trace!("{str}");
        }
        res
    }
}

pub type Symb<'a> = utils::string_ref::StrRef<'a, CryptoVampireStrValidator>;

pub mod path;
use path::{ISymb, Path};

mod squirrel_dump;
pub use squirrel_dump::{ProcessedSquirrelDump, SquirrelDump};
pub use term::*;
mod term;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Ident<'a> {
    #[serde(borrow)]
    pub name: Symb<'a>,
    // ignored
    // pub tag: i32,
}

impl<'a> Ident<'a> {
    pub fn name(&self) -> Symb<'a> {
        self.name.clone()
    }
}

impl<'a> Display for Ident<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { name, .. } = self;
        write!(f, "{name}")
    }
}

pub mod sort;
pub use sort::Type;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// #[serde(rename_all = "PascalCase")]
pub struct Variable<'a> {
    #[serde(borrow)]
    id: Ident<'a>,
    #[serde(rename = "ty")]
    sort: Box<Type<'a>>,
}

impl<'a> Variable<'a> {
    pub fn sort(&self) -> &Type<'a> {
        &self.sort
    }

    pub fn is_dummy(&self) -> bool {
        self.to_str_ref().as_str() == DUMMY_VAR
    }

    pub fn original_name_mut(&mut self) -> &mut Symb<'a> {
        &mut self.id.name
    }
    pub fn original_name(&self) -> &Symb<'a> {
        &self.id.name
    }
}

impl<'a> Sanitizable<'a> for Variable<'a> {
    fn to_str_ref(&self) -> StrRef<'a> {
        self.id.name().drop_guard()
    }

    fn sanitize_kind(&self) -> SanitizeKind {
        SanitizeKind::Variable
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct TypeVariable<'a> {
    #[serde(flatten, borrow)]
    pub id: Ident<'a>,
}

impl<'a> Sanitizable<'a> for TypeVariable<'a> {
    fn to_str_ref(&self) -> StrRef<'a> {
        self.id.name().drop_guard()
    }

    fn sanitize_kind(&self) -> SanitizeKind {
        SanitizeKind::Variable
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]

pub struct Channel<'a>(#[serde(borrow)] Path<'a>);

pub mod action;
pub use action::Action;

mod content;
pub use content::{Content, ContentRef};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct FunctionType<'a> {
    #[serde(borrow)]
    pub vars: Vec<TypeVariable<'a>>,
    pub args: Vec<Type<'a>>,
    pub out: Type<'a>,
}

new_name!(NameName:Name);
pub type Name<'a> = Content<NameName<'a>, FunctionType<'a>>;

pub mod operator;
pub use operator::Operator;

pub mod mmacro;
pub use mmacro::{Macro, MacroRef};

pub mod mtype;
pub use mtype::Sort;
use utils::string_ref::StrRef;

use super::{Sanitizable, SanitizeKind};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct CryptoVampireCall<'a> {
    pub parameters: Parameters,
    #[serde(borrow = "'a")]
    pub context: SquirrelDump<'a>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Parameters {
    pub num_retry: u32,
    pub timeout: f64,
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::BufReader;

    use paste::paste;

    use super::CryptoVampireCall;
    const ROOT: &'static str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");

    macro_rules! test_json_parser {
        ($f:ident :  $t:ty) => {
            paste! {
                    #[test]
                    #[allow(elided_lifetimes_in_paths)]
                    fn [<parse_$f>]() {
                        let file_path = format!("{ROOT}/tests/rust/squirrel-json-parsing/{}.json", stringify!($f));
                        println!("trying to parse {file_path}...");
                        let content = File::open(file_path).expect("Unable to read file");
                        let deserializer = &mut serde_json::Deserializer::from_reader(BufReader::new(content));
                        let result: Result<$t, _> = serde_path_to_error::deserialize(deserializer);
                        result.unwrap();
                    }
                }
        };
    }

    test_json_parser!(full1:CryptoVampireCall);
    test_json_parser!(canauth:CryptoVampireCall);
    // test_json_parser!(term1:Term);
}
