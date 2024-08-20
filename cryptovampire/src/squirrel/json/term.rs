use utils::implvec;

use super::*;
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

impl<'a> Term<'a> {
    pub fn mk_app<S>(s: S, args: implvec!(Self)) -> Self
    where
        Path<'a>: From<S>,
    {
        Self::App {
            f: Box::new(Self::Fun { symb: s.into() }),
            args: args.into_iter().collect(),
        }
    }
}
