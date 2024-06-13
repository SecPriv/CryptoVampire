use std::fmt::Display;

use anyhow::{anyhow, bail};

use cryptovampire_lib::{
    environement::traits::Realm,
    formula::{
        formula::RichFormula,
        function::{
            builtin::{EQUALITY, NOT, NOT_TA},
            signature::Signature,
            Function,
        },
        sort::sort_proxy::SortProxy,
        variable::Variable,
    },
};
use hashbrown::HashMap;
use itertools::Itertools;
use tptp::{
    cnf::{Disjunction, Literal},
    fof::*,
    Parse,
};
use utils::{match_as_trait, string_ref::StrRef};

// I need to remove the `'` from some function names
fn trim_quotes(str: String) -> String {
    let mut chars = str.chars();
    match (chars.next(), str.chars().last()) {
        (Some('\''), Some('\'')) => chars.take(str.len() - 2).collect(),
        _ => str,
    }
}

// TODO: remove error
macro_rules! mtry_from {
    ($l:lifetime, $name:ty; |$value:ident| $b:block) => {
        impl<$l> TryFrom<$name> for TmpFormula {
            type Error = anyhow::Error;

            fn try_from($value: $name) -> Result<Self, Self::Error> {
                $b
            }
        }
    };
}

macro_rules! final_term_like {
    ($name:ident) => {
        mtry_from!('a, $name<'a>; |value| {
            Ok(match value {
                $name::Constant(c) => Self::new_const(trim_quotes(c.to_string())),
                $name::Function(f, args) => {
                    let Arguments(args) = *args;
                    let rargs: Result<Vec<_>, _> = args.into_iter().map(|x| x.try_into()).collect();
                    Self::new(trim_quotes(f.to_string()), rargs?)
                }
            })
        });
    };
    ($($name:ident),*,) => {
        $(final_term_like!($name);)*
    }
}

macro_rules! continue_term_like {
    ($name:ident) => {
        mtry_from!('a, $name<'a>; |value| {
            TryFrom::try_from(value.0)
        });
    };
    ($($name:ident),*,) => {
        $(continue_term_like!($name);)*
    }
}

/// A very simplified AST from the [tptp] crate.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TmpFormula {
    App { head: String, args: Vec<TmpFormula> },
    Var(String),
}
final_term_like!(PlainTerm, SystemTerm, DefinedPlainTerm,);
continue_term_like!(
    SystemAtomicFormula,
    DefinedPlainFormula,
    PlainAtomicFormula,
    DefinedAtomicTerm,
);

mtry_from!('a, Literal<'a>; |value| {
    match value {
        Literal::Atomic(a) => a.try_into(),
        Literal::NegatedAtomic(a) => Ok(TmpFormula::new(
            NOT_TA.name().to_string(),
            vec![a.try_into()?],
        )),
        Literal::Infix(i) => i.try_into(),
    }
});

impl<'a> TryFrom<InfixUnary<'a>> for TmpFormula {
    type Error = anyhow::Error;
    fn try_from(value: InfixUnary<'a>) -> Result<Self, Self::Error> {
        {
            let left: TmpFormula = (*value.left).try_into()?;
            let right: TmpFormula = (*value.right).try_into()?;
            Ok(TmpFormula::new(
                NOT.name().to_string(),
                vec![TmpFormula::new(
                    EQUALITY.name().to_string(),
                    vec![left, right],
                )],
            ))
        }
    }
}

mtry_from!('a, AtomicFormula<'a>; |value| {
    match_as_trait!(AtomicFormula, |x| in value => Plain | Defined | System {x.try_into()})
});

mtry_from!('a, FunctionTerm<'a>; |value| {
    match_as_trait!(FunctionTerm, |x| in value => Plain | Defined | System {x.try_into()})
});

mtry_from!('a, tptp::fof::Term<'a>; |value| {
    match value {
        Term::Function(f) => (*f).try_into(),
        Term::Variable(v) => Ok(TmpFormula::Var(v.to_string())),
    }
});

mtry_from!('a, DefinedAtomicFormula<'a>; |value| {
    match value {
        DefinedAtomicFormula::Plain(df) => df.try_into(),
        DefinedAtomicFormula::Infix(dif) => dif.try_into(),
    }
});

mtry_from!('a, DefinedInfixFormula<'a>; |value| {
    let left: TmpFormula = (*value.left).try_into()?;
    let right: TmpFormula = (*value.right).try_into()?;
    Ok(TmpFormula::new(
        EQUALITY.name().to_string(),
        vec![left, right]
    ))
});

mtry_from!('a, DefinedTerm<'a>; |value| {
    match value {
        DefinedTerm::Defined(d) => Ok(TmpFormula::new_const(d.to_string())),
        DefinedTerm::Atomic(a) => a.try_into(),
    }
});

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

    pub fn parse_disjunction(str: &str) -> anyhow::Result<Vec<Self>> {
        let str = format!("{}.", str);
        let disjunction: tptp::Result<Disjunction, ()> = Disjunction::parse(str.as_bytes());
        let litteral = match disjunction {
            Ok((_, Disjunction(l))) => l,
            Err(e) => bail!("{}", e),
        };

        litteral.into_iter().map(|l| l.try_into()).collect()
    }

    pub fn parse(str: &str) -> anyhow::Result<Self> {
        let str = format!("{}.", str);
        let litteral: tptp::Result<Literal, ()> = Literal::parse(str.as_bytes());
        match litteral {
            Ok((_, l)) => l.try_into(),
            Err(e) => bail!("{}", e),
        }
    }

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