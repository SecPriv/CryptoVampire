use std::fmt::Display;

use anyhow::{anyhow, bail};
use utils::string_ref::StrRef;

use crate::{
    environement::traits::Realm,
    formula::{
        formula::RichFormula,
        function::{signature::Signature, Function},
        sort::sort_proxy::SortProxy,
        variable::Variable,
    },
};
use hashbrown::HashMap;
use itertools::Itertools;

/// A very simplified AST
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TmpFormula {
    App { head: String, args: Vec<TmpFormula> },
    Var(String),
}

impl TmpFormula {
    pub fn new(head: String, args: Vec<TmpFormula>) -> Self {
        Self::App { head, args }
    }

    pub fn new_const(head: String) -> Self {
        Self::App { head, args: vec![] }
    }
    pub fn new_ref(head: &str, args: &[TmpFormula]) -> Self {
        Self::new(head.to_string(), args.to_vec())
    }

    // pub fn parse_disjunction(str: &str) -> anyhow::Result<Vec<Self>> {
    //     let str = format!("{}.", str);
    //     let disjunction: tptp::Result<Disjunction, ()> = Disjunction::parse(str.as_bytes());
    //     let litteral = match disjunction {
    //         Ok((_, Disjunction(l))) => l,
    //         Err(e) => bail!("{}", e),
    //     };

    //     litteral.into_iter().map(|l| l.try_into()).collect()
    // }

    // pub fn parse(str: &str) -> anyhow::Result<Self> {
    //     let str = format!("{}.", str);
    //     let litteral: tptp::Result<Literal, ()> = Literal::parse(str.as_bytes());
    //     match litteral {
    //         Ok((_, l)) => l.try_into(),
    //         Err(e) => bail!("{}", e),
    //     }
    // }

    pub fn head(&self) -> Option<&str> {
        match self {
            Self::App { head, .. } => Some(head),
            _ => None,
        }
    }

    pub fn args(&self) -> Option<&[TmpFormula]> {
        match self {
            Self::App { args, .. } => Some(args.as_ref()),
            _ => None,
        }
    }

    pub fn to_rich_formula<'a, 'bump>(
        &'a self,
        functions: &HashMap<StrRef<'bump>, Function<'bump>>,
        expected_sort: SortProxy<'bump>,
        variables: &mut HashMap<&'a Self, Variable<'bump>>,
    ) -> anyhow::Result<RichFormula<'bump>> {
        let realm = &Realm::Symbolic;
        let head = self.head();
        let f = head.and_then(|head| functions.get(head));
        if let Some(f) = f {
            if f.is_tmp() {
                bail!("tmp function")
            }
            let _head = head.unwrap(); // can't fail bc of check on f
            let sign = f.signature();
            sign.out()
                .unify(&expected_sort, realm)
                .map_err(|_| anyhow!("infernce error"))?;
            let mut args = vec![];
            for e in self.args().unwrap().iter().zip_longest(sign.args()) {
                match e {
                    itertools::EitherOrBoth::Left(_) => {
                        bail!("more arguments that expected in {:}", &self)
                    }
                    itertools::EitherOrBoth::Right(_) => break,
                    itertools::EitherOrBoth::Both(arg, sort) => {
                        args.push(arg.to_rich_formula(functions, sort, variables)?.into_arc())
                    }
                }
            }
            Ok(RichFormula::Fun(*f, args.into()))
        } else {
            if let Some(&v) = variables
                .get(self)
                .and_then(|v| expected_sort.expects(*v.sort(), realm).ok().map(|_| v))
            {
                Ok(RichFormula::Var(v))
            } else if let Some(s) = expected_sort.as_option() {
                let i = variables.len();

                // i is fresh
                debug_assert!(variables.values().map(|v| v.id()).all(|j| i != j));

                let v = Variable::new(i, s);
                variables.insert(self, v);
                Ok(RichFormula::Var(v))
            } else {
                bail!("inference error")
            }
        }
    }
}

impl Display for TmpFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TmpFormula::App { head, args } => {
                write!(f, "{:}(", &head)?;
                for arg in args {
                    write!(f, "{:}, ", arg)?;
                }
                write!(f, ")")
            }
            TmpFormula::Var(s) => s.fmt(f),
        }
    }
}
