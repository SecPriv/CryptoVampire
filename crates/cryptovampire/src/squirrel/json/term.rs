use action::ActionName;
use itertools::chain;
use operator::OperatorName;
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
pub enum Term<'a> {
    App {
        #[serde(borrow)]
        f: Box<Term<'a>>,
        args: Vec<Term<'a>>,
    },
    Fun {
        symb: OperatorName<'a>,
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
        symb: ActionName<'a>,
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

impl<'a> Diff<'a> {
    pub fn term(&self) -> &Term<'a> {
        &self.term
    }
}

impl<'a> Term<'a> {
    pub fn mk_app<S>(s: S, args: implvec!(Self)) -> Self
    where
        Path<'a>: From<S>,
    {
        Self::App {
            f: Box::new(Self::Fun {
                symb: OperatorName(s.into()),
            }),
            args: args.into_iter().collect(),
        }
    }

    /// Iterate over all subterms of [self]
    pub fn iter(&self) -> impl Iterator<Item = &'_ Self> {
        SubTermIterator { pile: vec![self] }
    }

    /// Iterate over all variable appering in [self]
    /// (makes no distinction between bound and unbound variables)
    pub fn vars<'b>(&'b self) -> impl Iterator<Item = &'b Variable<'a>> {
        self.iter().filter_map(|t| match t {
            Term::Var { var } => Some(var),
            _ => None,
        })
    }
}

struct SubTermIterator<'a, 'b> {
    pile: Vec<&'b Term<'a>>,
}

impl<'a, 'b> Iterator for SubTermIterator<'a, 'b> {
    type Item = &'b Term<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.pile.pop().inspect(|&t| {
            match t {
                Term::Fun { .. } | Term::Var { .. } => (),
                Term::Action { args, .. } | Term::Name { args, .. } => {
                    self.pile.extend(args.iter())
                }
                Term::App { args, f: e }
                | Term::Macro {
                    args, timestamp: e, ..
                } => self.pile.extend(chain!(args.iter(), [e.as_ref()])),
                Term::Let { decl, body, .. } => self.pile.extend([decl, body].map(Box::as_ref)),
                Term::Tuple { elements } => self.pile.extend(elements.iter()),
                Term::Quant { body, .. } | Term::Proj { body, .. } => self.pile.push(body.as_ref()),
                Term::Find {
                    condition,
                    success,
                    faillure,
                    ..
                } => self
                    .pile
                    .extend([condition, success, faillure].map(Box::as_ref)),
                Term::Diff { terms } => self.pile.extend(terms.iter().map(Diff::term)),
            };
        })
    }
}
