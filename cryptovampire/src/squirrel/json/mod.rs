use std::{borrow::Cow, fmt::Display};

use cryptovampire_lib::formula::variable::uvar;
use serde::{Deserialize, Serialize};
pub use path::Pathed;

/// Forbiden characters in cv's input
const FORBIDDEN: &'static str = ";$#";

pub trait Named<'a> {
    fn name(&self) -> Symb<'a>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct CryptoVampireStrValidator;

impl utils::string_ref::Validator for CryptoVampireStrValidator {
    fn validate(&self, str: &str) -> bool {
        !str.chars().any(|x| FORBIDDEN.contains(x))
    }
}

pub type Symb<'a> = utils::string_ref::StrRef<'a, CryptoVampireStrValidator>;

pub mod path;
use path::{ISymb, Path};

mod squirrel_dump;
pub use squirrel_dump::{SquirrelDump, ProcessedSquirrelDump};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Quant {
    ForAll,
    Exists,
    Seq,
    Lambda,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(tag = "constructor")]
pub enum Term<'a> {
    App {
        #[serde(borrow)]
        f: Box<Term<'a>>,
        args: Vec<Term<'a>>,
    },
    Fun {
        symb: Path<'a>,
    },
    Name {
        #[serde(borrow)]
        symb: ISymb<'a>,
        args: Vec<Term<'a>>,
    },
    Macro {
        #[serde(borrow)]
        symb: ISymb<'a>,
        args: Vec<Term<'a>>,
        timestamp: Box<Term<'a>>,
    },
    Action {
        #[serde(borrow)]
        symb: Path<'a>,
        args: Vec<Term<'a>>,
    },
    Var {
        #[serde(flatten, borrow)]
        var: Variable<'a>,
    },
    Let {
        var: Box<Term<'a>>,
        decl: Box<Term<'a>>,
        body: Box<Term<'a>>,
    },
    Tuple {
        elements: Vec<Term<'a>>,
    },
    Proj {
        id: u8,
        body: Box<Term<'a>>,
    },
    Diff {
        terms: Vec<Diff<'a>>,
    },
    Find {
        vars: Vec<Term<'a>>,
        condition: Box<Term<'a>>,
        success: Box<Term<'a>>,
        faillure: Box<Term<'a>>,
    },
    Quant {
        quantificator: Quant,
        vars: Vec<Term<'a>>,
        body: Box<Term<'a>>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// #[serde(rename_all = "PascalCase")]
pub struct Diff<'a> {
    #[serde(borrow)]
    pub proj: Symb<'a>,
    pub term: Term<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Ident<'a> {
    #[serde(borrow)]
    pub name: Symb<'a>,
    pub tag: i32,
}

impl<'a> Named<'a> for Ident<'a> {
    fn name(&self) -> Symb<'a> {
        self.name.clone()
    }
}

impl<'a> Display for Ident<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { name, tag } = self;
        write!(f, "{name}_{tag:}")
    }
}

pub mod sort;
pub use sort::Type;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// #[serde(rename_all = "PascalCase")]
pub struct Variable<'a> {
    #[serde(borrow)]
    pub id: Ident<'a>,
    #[serde(rename = "ty")]
    pub sort: Box<Type<'a>>,
}

impl<'a> Named<'a> for Variable<'a> {
    fn name(&self) -> Symb<'a> {
        self.id.name()
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct TypeVariable<'a> {
    #[serde(flatten, borrow)]
    pub id: Ident<'a>,
}

impl<'a> Named<'a> for TypeVariable<'a> {
    fn name(&self) -> Symb<'a> {
        self.id.name()
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]

pub struct Channel<'a>(#[serde(borrow)] Path<'a>);
impl<'a> Pathed<'a> for Channel<'a> {
    fn path(&self) -> &Path<'a> {
        &self.0
    }
}

pub mod action;
pub use action::Action;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Content<'a, U> {
    #[serde(borrow)]
    pub symb: Path<'a>,
    pub data: U,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct FunctionType<'a> {
    #[serde(borrow)]
    pub vars: Vec<TypeVariable<'a>>,
    pub args: Vec<Type<'a>>,
    pub out: Type<'a>,
}

pub type Name<'a> = Content<'a, FunctionType<'a>>;

pub mod operator;
pub use operator::Operator;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct SingleSystem<'a> {
    #[serde(borrow)]
    system: Path<'a>,
    projection: Symb<'a>,
}

pub mod mmacro;
pub use mmacro::Macro;

pub mod mtype;
pub use mtype::Sort;

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
    use paste::paste;
    use std::{
        fs::{self, File},
        io::BufReader,
    };

    use crate::squirrel::json::action;

    use super::{CryptoVampireCall, SquirrelDump, Term, Type};

    macro_rules! test_json_parser {
        ($f:ident :  $t:ty) => {
            paste! {
                    #[test]
                    fn [<parse_$f>]() {
                        let file_path = format!("../tests/squirrel/{}.json", stringify!($f));
                        let content = File::open(file_path).expect("Unable to read file");
                        let deserializer = &mut serde_json::Deserializer::from_reader(BufReader::new(content));
                        let result: Result<$t, _> = serde_path_to_error::deserialize(deserializer);
                        result.unwrap();
                    }
                }
        };
    }

    // #[test]
    // fn types() {
    //     let t = Type::TBase("LP".into());
    //     assert_eq!("{\"TBase\":\"LP\"}", &serde_json::to_string(&t).unwrap());
    // }

    // #[test]
    // fn operator_def() {
    //     use super::operator::*;
    //     let t = DefaultDef::Abstract {
    //         abstract_def: AbstractDef::Abstract(SymbType::Infix(Assoc::Right)),
    //         associated_fun: vec![],
    //     };
    //     println!("{}", serde_json::to_string(&t).unwrap());
    //     assert_eq!(
    //         "{\"abstract_def\":{\"Abstract\":{\"Infix\":\"Right\"}},\"associated_fun\":[]}",
    //         &serde_json::to_string(&t).unwrap()
    //     );
    // }

    test_json_parser!(full1:CryptoVampireCall);
    // test_json_parser!(term1:Term);
}
