use cryptovampire_lib::formula::variable::uvar;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(rename_all = "PascalCase")]
pub struct SquirrelDump {
    conclusion: Box<Term>,
    hypotheses: Vec<Term>,
    variables: Vec<Variable>,
    functions: Vec<Operator>,
    names: Vec<Operator>,
    macros: Vec<Macro>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(rename_all = "PascalCase")]
pub enum Quant {
    ForAll,
    Exists,
    Seq,
    Lambda,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(tag = "Constructor", rename_all = "PascalCase")]
pub enum Term {
    #[serde(rename_all = "PascalCase")]
    App {
        fsymb: Box<Term>,
        arguments: Vec<Term>,
    },
    #[serde(rename_all = "PascalCase")]
    Fun { fname: String },
    #[serde(rename_all = "PascalCase")]
    Name { nsymb: String, arguments: Vec<Term> },
    #[serde(rename_all = "PascalCase")]
    Macro {
        msymb: String,
        arguments: Vec<Term>,
        timestamp: Box<Term>,
    },
    #[serde(rename_all = "PascalCase")]
    Action { asymb: String, arguments: Vec<Term> },
    #[serde(rename_all = "PascalCase")]
    Var { id: uvar, name: String },
    #[serde(rename_all = "PascalCase")]
    Let {
        var: Box<Term>,
        term1: Box<Term>,
        term2: Box<Term>,
    },
    #[serde(rename_all = "PascalCase")]
    Tuple { elements: Box<[Term; 2]> },
    #[serde(rename_all = "PascalCase")]
    Proj { id: u8, term: Box<Term> },
    #[serde(rename_all = "PascalCase")]
    Diff { terms: Vec<Diff> },
    #[serde(rename_all = "PascalCase")]
    Find {
        vars: Vec<Term>,
        term1: Box<Term>,
        term2: Box<Term>,
        term3: Box<Term>,
    },
    #[serde(rename_all = "PascalCase")]
    Quant {
        quantificator: Quant,
        vars: Vec<Term>,
        term: Box<Term>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(rename_all = "PascalCase")]
pub struct Diff {
    proj: String,
    term: Term,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(tag = "Constructor", rename_all = "PascalCase")]
pub enum Type {
    Message,
    Boolean,
    Index,
    Timestamp,
    #[serde(rename_all = "PascalCase")]
    TBase {
        string: String,
    },
    #[serde(rename_all = "PascalCase")]
    TVar {
        id: uvar,
        name: String,
    },
    #[serde(rename_all = "PascalCase")]
    TUnivar {
        id: String,
        name: String,
    },
    #[serde(rename_all = "PascalCase")]
    Tuple {
        elements: Vec<Type>,
    },
    #[serde(rename_all = "PascalCase")]
    Fun {
        type1: Box<Type>,
        type2: Box<Type>,
    },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(rename_all = "PascalCase")]
pub struct Variable {
    id: uvar,
    name: String,
    #[serde(rename = "Type")]
    sort: Box<Type>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(rename_all = "PascalCase")]
pub struct Operator {
    name: String,
    type_args: Vec<Type>,
    type_out: Box<Type>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(rename_all = "PascalCase")]
pub struct Macro {
    name: String,
    index_arity: usize,
    type_out: Box<Type>,
}

#[cfg(test)]
mod tests {
    use paste::paste;
    use std::{
        fs::{self, File},
        io::BufReader,
    };

    use super::{SquirrelDump, Term};

    #[test]
    fn serializing() {
        let v1 = Term::Var {
            id: 2,
            name: "t".into(),
        };
        let v2 = Term::Var {
            id: 3,
            name: "t".into(),
        };
        let t = Term::Quant {
            quantificator: super::Quant::ForAll,
            vars: vec![v1.clone(), v2.clone()],
            term: Box::new(Term::App {
                fsymb: Box::new(Term::Fun {
                    fname: "and".into(),
                }),
                arguments: vec![v1, v2],
            }),
        };
        let t = SquirrelDump {
            conclusion: Box::new(t.clone()),
            hypotheses: vec![],
            variables: vec![],
            functions: vec![],
            names: vec![],
            macros: vec![],
        };

        let result = "{\"Conclusion\":{\"Constructor\":\"Quant\",\"Quantificator\":\"ForAll\",\"Vars\":[{\"Constructor\":\"Var\",\"Id\":2,\"Name\":\"t\"},{\"Constructor\":\"Var\",\"Id\":3,\"Name\":\"t\"}],\"Term\":{\"Constructor\":\"App\",\"Fsymb\":{\"Constructor\":\"Fun\",\"Fname\":\"and\"},\"Arguments\":[{\"Constructor\":\"Var\",\"Id\":2,\"Name\":\"t\"},{\"Constructor\":\"Var\",\"Id\":3,\"Name\":\"t\"}]}},\"Hypotheses\":[],\"Variables\":[],\"Functions\":[],\"Names\":[],\"Macros\":[]}";
        let parsed = serde_json::to_string(&t).unwrap();

        assert_eq!(result, parsed);
    }

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

    test_json_parser!(full1:SquirrelDump);
    test_json_parser!(term1:Term);
}
