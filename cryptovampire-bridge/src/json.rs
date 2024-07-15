use cryptovampire_lib::formula::variable::uvar;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct SquirrelDump {
    query: Box<Term>,
    hypotheses: Vec<Term>,
    variables: Vec<Variable>,
    actions: Vec<Action>,
    names: Vec<Name>,
    operators: Vec<Operator>,
    macros: Vec<Macro>,
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
pub enum Term {
    // #[serde(rename_all = "PascalCase")]
    App {
        f: Box<Term>,
        args: Vec<Term>,
    },
    // #[serde(rename_all = "PascalCase")]
    Fun {
        symb: String,
    },
    // #[serde(rename_all = "PascalCase")]
    Name {
        symb: String,
        args: Vec<Term>,
    },
    // #[serde(rename_all = "PascalCase")]
    Macro {
        symb: String,
        args: Vec<Term>,
        timestamp: Box<Term>,
    },
    // #[serde(rename_all = "PascalCase")]
    Action {
        symb: String,
        args: Vec<Term>,
    },
    // #[serde(rename_all = "PascalCase")]
    Var {
        #[serde(flatten)]
        var: Variable
    },
    // #[serde(rename_all = "PascalCase")]
    Let {
        var: Box<Term>,
        decl: Box<Term>,
        body: Box<Term>,
    },
    // #[serde(rename_all = "PascalCase")]
    Tuple {
        elements: Vec<Term>,
    },
    // #[serde(rename_all = "PascalCase")]
    Proj {
        id: u8,
        body: Box<Term>,
    },
    // #[serde(rename_all = "PascalCase")]
    Diff {
        terms: Vec<Diff>,
    },
    // #[serde(rename_all = "PascalCase")]
    Find {
        vars: Vec<Term>,
        condition: Box<Term>,
        success: Box<Term>,
        faillure: Box<Term>,
    },
    // #[serde(rename_all = "PascalCase")]
    Quant {
        quantificator: Quant,
        vars: Vec<Term>,
        body: Box<Term>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// #[serde(rename_all = "PascalCase")]
pub struct Diff {
    proj: String,
    term: Term,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Ident {
    name: String,
    tag: i32,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Type {
    Message,
    Boolean,
    Index,
    Timestamp,
    // #[serde(rename_all = "PascalCase")]
    TBase(String),
    // #[serde(rename_all = "PascalCase")]
    TVar {
        #[serde(flatten)]
        ident: Ident,
    },
    // #[serde(rename_all = "PascalCase")]
    TUnivar {
        #[serde(flatten)]
        ident: Ident,
    },
    // #[serde(rename_all = "PascalCase")]
    Tuple {
        elements: Vec<Type>,
    },
    // #[serde(rename_all = "PascalCase")]
    Fun {
        #[serde(rename = "in")]
        t_in: Box<Type>,
        out: Box<Type>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// #[serde(rename_all = "PascalCase")]
pub struct Variable {
    id: Ident,
    #[serde(rename = "ty")]
    sort: Box<Type>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct TypeVariable {
    #[serde(flatten)]
    id: Ident,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Channel(String);

pub mod action {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Condition {
        vars: Vec<Variable>,
        term: Term,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Ouptut {
        channel: Channel,
        term: Term,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Update {
        symb: String,
        args: Vec<Term>,
        body: Term,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Item<A>{
        par_choice: (u32, A),
        sum_choice: (u32, A)
    }

    pub type T<A> = Vec<Item<A>>;

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Action {
        name: String,
        action: T<Vec<Variable>>, // this is an `action_v`
        input: Channel,
        indices: Vec<Variable>,
        condition: Condition,
        updates: Vec<Term>,
        output: Ouptut,
        globals: Vec<String>,
    }
}
pub use action::Action;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Content<U> {
    symb: String,
    data: U,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct FunctionType {
    vars: Vec<TypeVariable>,
    args: Vec<Type>,
    out: Type,
}

pub type Name = Content<FunctionType>;
pub mod operator {
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
    pub struct Concrete {
        name: String,
        type_variables: Vec<TypeVariable>,
        args: Vec<Variable>,
        out_type: Type,
        body: Term,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    #[serde(untagged)]
    pub enum Def {
        Abstract {
            abstract_def: AbstractDef,
            associated_fun: Vec<String>,
        },
        Concrete(Concrete),
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Data {
        #[serde(rename = "type")]
        sort: FunctionType,
        def: Def,
    }
}
pub type Operator = Content<operator::Data>;

mod mmacro {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub enum Data {
        Input,
        Output,
        Cond,
        Exec,
        Frame,
        Global,
        State {
            arity: usize,
            #[serde(rename = "type")]
            sort: Type,
        },
    }
}
pub type Macro = Content<mmacro::Data>;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct CryptoVampireCall {
    parameters: Parameters,
    context: SquirrelDump,
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
        let t = Def::Abstract { abstract_def: 
                AbstractDef::Abstract(SymbType::Infix(Assoc::Right))
            
            , associated_fun: vec![] };
        println!("{}", serde_json::to_string(&t).unwrap());
        assert_eq!("{\"abstract_def\":{\"Abstract\":{\"Infix\":\"Right\"}},\"associated_fun\":[]}", &serde_json::to_string(&t).unwrap());
    }

    test_json_parser!(full4:CryptoVampireCall);
    test_json_parser!(term1:Term);
}
