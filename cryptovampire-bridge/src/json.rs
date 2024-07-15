use std::borrow::Cow;

use cryptovampire_lib::formula::variable::uvar;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct SquirrelDump<'a> {
    #[serde(borrow)]
    query: Box<Term<'a>>,
    hypotheses: Vec<Term<'a>>,
    variables: Vec<Variable<'a>>,
    actions: Vec<Action<'a>>,
    names: Vec<Name<'a>>,
    operators: Vec<Operator<'a>>,
    macros: Vec<Macro<'a>>,
}

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
    // #[serde(rename_all = "PascalCase")]
    App {
        f: Box<Term<'a>>,
        args: Vec<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Fun {
        symb: Cow<'a, str>,
    },
    // #[serde(rename_all = "PascalCase")]
    Name {
        symb: Cow<'a, str>,
        args: Vec<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Macro {
        symb: Cow<'a, str>,
        args: Vec<Term<'a>>,
        timestamp: Box<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Action {
        symb: Cow<'a, str>,
        args: Vec<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Var {
        #[serde(flatten, borrow)]
        var: Variable<'a>,
    },
    // #[serde(rename_all = "PascalCase")]
    Let {
        var: Box<Term<'a>>,
        decl: Box<Term<'a>>,
        body: Box<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Tuple {
        elements: Vec<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Proj {
        id: u8,
        body: Box<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Diff {
        terms: Vec<Diff<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Find {
        vars: Vec<Term<'a>>,
        condition: Box<Term<'a>>,
        success: Box<Term<'a>>,
        faillure: Box<Term<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Quant {
        quantificator: Quant,
        vars: Vec<Term<'a>>,
        body: Box<Term<'a>>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// #[serde(rename_all = "PascalCase")]
pub struct Diff<'a> {
    pub proj: Cow<'a, str>,
    #[serde(borrow)]
    pub term: Term<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Ident<'a> {
    name: Cow<'a, str>,
    tag: i32,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Type<'a> {
    Message,
    Boolean,
    Index,
    Timestamp,
    // #[serde(rename_all = "PascalCase")]
    TBase(Cow<'a, str>),
    // #[serde(rename_all = "PascalCase")]
    TVar {
        #[serde(flatten)]
        ident: Ident<'a>,
    },
    // #[serde(rename_all = "PascalCase")]
    TUnivar {
        #[serde(flatten)]
        ident: Ident<'a>,
    },
    // #[serde(rename_all = "PascalCase")]
    Tuple {
        elements: Vec<Type<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Fun {
        #[serde(rename = "in")]
        t_in: Box<Type<'a>>,
        out: Box<Type<'a>>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// #[serde(rename_all = "PascalCase")]
pub struct Variable<'a> {
    #[serde(borrow)]
    id: Ident<'a>,
    #[serde(rename = "ty")]
    sort: Box<Type<'a>>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct TypeVariable<'a> {
    #[serde(flatten, borrow)]
    id: Ident<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Channel<'a>(Cow<'a, str>);

pub mod action {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Condition<'a> {
        #[serde(borrow)]
        vars: Vec<Variable<'a>>,
        term: Term<'a>,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Ouptut<'a> {
        #[serde(borrow)]
        channel: Channel<'a>,
        term: Term<'a>,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Update<'a> {
        symb: Cow<'a, str>,
        #[serde(borrow)]
        args: Vec<Term<'a>>,
        body: Term<'a>,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Item<A> {
        par_choice: (u32, A),
        sum_choice: (u32, A),
    }

    pub type T<A> = Vec<Item<A>>;

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Action<'a> {
        name: Cow<'a, str>,
        #[serde(borrow)]
        action: T<Vec<Variable<'a>>>, // this is an `action_v`
        input: Channel<'a>,
        indices: Vec<Variable<'a>>,
        condition: Condition<'a>,
        updates: Vec<Term<'a>>,
        output: Ouptut<'a>,
        globals: Vec<Cow<'a, str>>,
    }
}
pub use action::Action;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Content<'a, U> {
    symb: Cow<'a, str>,
    data: U,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct FunctionType<'a> {
    #[serde(borrow)]
    vars: Vec<TypeVariable<'a>>,
    args: Vec<Type<'a>>,
    out: Type<'a>,
}

pub type Name<'a> = Content<'a, FunctionType<'a>>;
pub mod operator {
    use std::borrow::Cow;

    use serde::{Deserialize, Serialize};

    use super::*;

    #[allow(non_camel_case_types)]
    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
    pub enum DhHyp {
        DH_DDH,
        DH_CDH,
        DH_GDH,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
    pub enum Assoc {
        Right,
        Left,
        NonAssoc,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
    pub enum SymbType {
        Prefix,
        Infix(Assoc),
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub enum AbstractDef {
        Hash,
        DHgen(Vec<DhHyp>),
        AEnc,
        ADec,
        SEnc,
        SDec,
        Sign,
        CheckSign,
        PublicKey,
        Abstract(SymbType),
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Concrete<'a> {
        name: Cow<'a, str>,
        #[serde(borrow)]
        type_variables: Vec<TypeVariable<'a>>,
        args: Vec<Variable<'a>>,
        out_type: Type<'a>,
        body: Term<'a>,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    #[serde(untagged)]
    pub enum Def<'a> {
        Abstract {
            abstract_def: AbstractDef,
            #[serde(borrow)]
            associated_fun: Vec<Cow<'a, str>>,
        },
        Concrete(Concrete<'a>),
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Data<'a> {
        #[serde(rename = "type", borrow)]
        sort: FunctionType<'a>,
        def: Def<'a>,
    }
}
pub type Operator<'a> = Content<'a, operator::Data<'a>>;

mod mmacro {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub enum Data<'a> {
        Input,
        Output,
        Cond,
        Exec,
        Frame,
        Global,
        State {
            arity: usize,
            #[serde(rename = "type", borrow)]
            sort: Type<'a>,
        },
    }
}
pub type Macro<'a> = Content<'a, mmacro::Data<'a>>;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct CryptoVampireCall<'a> {
    parameters: Parameters,
    #[serde(borrow = "'a")]
    context: SquirrelDump<'a>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Parameters {
    num_retry: u32,
    timeout: f64,
}

#[cfg(test)]
mod tests {
    use paste::paste;
    use std::{
        fs::{self, File},
        io::BufReader,
    };

    use crate::json::action;

    use super::{CryptoVampireCall, SquirrelDump, Term, Type};

    macro_rules! test_json_parser {
        ($f:ident :  $t:ty) => {
            paste! {
                    #[test]
                    fn [<parse_$f>]() {
                        let file_path = format!("tests/assets/squirrel-output/{}.json", stringify!($f));
                        let content = File::open(file_path).expect("Unable to read file");
                        let deserializer = &mut serde_json::Deserializer::from_reader(BufReader::new(content));
                        let result: Result<$t, _> = serde_path_to_error::deserialize(deserializer);
                        result.unwrap();
                    }
                }
        };
    }

    #[test]
    fn types() {
        let t = Type::TBase("LP".into());
        assert_eq!("{\"TBase\":\"LP\"}", &serde_json::to_string(&t).unwrap());
    }

    #[test]
    fn operator_def() {
        use super::operator::*;
        let t = Def::Abstract {
            abstract_def: AbstractDef::Abstract(SymbType::Infix(Assoc::Right)),
            associated_fun: vec![],
        };
        println!("{}", serde_json::to_string(&t).unwrap());
        assert_eq!(
            "{\"abstract_def\":{\"Abstract\":{\"Infix\":\"Right\"}},\"associated_fun\":[]}",
            &serde_json::to_string(&t).unwrap()
        );
    }

    test_json_parser!(full4:CryptoVampireCall);
    test_json_parser!(term1:Term);
}
