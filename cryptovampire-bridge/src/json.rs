use cryptovampire_lib::formula::variable::uvar;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(rename_all = "PascalCase")]
pub struct SquirrelDump {
    condition: Box<Term>,
    hypetheses: Vec<Term>,
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
    App {
        asymb: Box<Term>,
        arguements: Vec<Term>,
    },
    Fun {
        name: String,
    },
    Name {
        fsymb: String,
        arguements: Vec<Term>,
    },
    Macro {
        msymb: String,
        arguements: Vec<Term>,
        timestamp: Box<Term>,
    },
    Action {
        asymb: String,
        arguements: Vec<Term>,
    },
    Var {
        id: uvar,
        name: String,
    },
    Let {
        var: Box<Term>,
        term1: Box<Term>,
        term2: Box<Term>,
    },
    Tuple {
        elements: Box<[Term; 2]>,
    },
    Proj {
        id: u8,
        term: Box<Term>,
    },
    Diff {
        terms: Vec<Diff>,
    },
    Find {
        vars: Vec<Term>,
        term1: Box<Term>,
        term2: Box<Term>,
        term3: Box<Term>,
    },
    Quant {
        quantficator: Quant,
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
    TBase(String),
    TVar { id: uvar, name: String },
    TUnivar { id: String, name: String },
    Tuple { elements: Vec<Type> },
    Fun { type1: Box<Type>, type2: Box<Type> },
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
    use super::{SquirrelDump, Term};

    #[test]
    fn testing() {
        let v1 = Term::Var {
            id: 2,
            name: "t".into(),
        };
        let v2 = Term::Var {
            id: 3,
            name: "t".into(),
        };
        let t = Term::Quant {
            quantficator: super::Quant::ForAll,
            vars: vec![v1.clone(), v2.clone()],
            term: Box::new(Term::App {
                asymb: Box::new(Term::Fun { name: "and".into() }),
                arguements: vec![v1, v2],
            }),
        };
        let t = SquirrelDump {
            condition: Box::new(t.clone()),
            hypetheses: vec![],
            variables: vec![],
            functions: vec![],
            names: vec![],
            macros: vec![],
        };

        println!("{}", serde_json::to_string(&t).unwrap())
    }
}
