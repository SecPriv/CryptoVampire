//! tptp parsing
//!
//! This is an interface with the [tptp] crate. We need this to read the output of `vampire`.
use crate::formula::TmpFormula;
use crate::formula::function::builtin::{EQUALITY, NOT, NOT_TA};

struct A(TmpFormula);

impl From<A> for TmpFormula {
    fn from(val: A) -> Self {
        val.0
    }
}

pub trait TptpParse {
    fn parse(str: &str) -> crate::Result<Self>
    where
        Self: Sized;
}

impl TptpParse for TmpFormula {
    fn parse(str: &str) -> crate::Result<Self> {
        let str = format!("{}.", str.trim());
        #[allow(elided_lifetimes_in_paths)]
        let litteral: tptp::Result<Literal, ()> = Literal::parse(str.as_bytes());
        let (_, l) = litteral?;
        let tmp: A = l.try_into()?;
        Ok(tmp.0)
    }
}

use itertools::Itertools;
use tptp::Parse;
use tptp::cnf::Literal;
use tptp::fof::*;
use utils::{implvec, match_as_trait};

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
    ($l:lifetime, $name:ty; | $value:ident | $b:block) => {
        impl<$l> TryFrom<$name> for A {
            type Error = crate::Error;

            fn try_from($value: $name) -> crate::Result<Self> {
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
                    let rargs: Result<Vec<A>, _> = args.into_iter().map(|x| x.try_into()).collect();
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
        Literal::NegatedAtomic(a) => Ok(A::new(
            NOT_TA.name().to_string(),
            [A::try_from(a)?],
        )),
        Literal::Infix(i) => i.try_into(),
    }
});

impl<'a> TryFrom<InfixUnary<'a>> for A {
    type Error = crate::Error;
    fn try_from(value: InfixUnary<'a>) -> Result<Self, Self::Error> {
        {
            let left: A = (*value.left).try_into()?;
            let right: A = (*value.right).try_into()?;
            Ok(A::new(
                NOT.name().to_string(),
                vec![A::new(EQUALITY.name().to_string(), vec![left, right])],
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
        Term::Variable(v) => Ok(A(TmpFormula::Var(v.to_string()))),
    }
});

mtry_from!('a, DefinedAtomicFormula<'a>; |value| {
    match value {
        DefinedAtomicFormula::Plain(df) => df.try_into(),
        DefinedAtomicFormula::Infix(dif) => dif.try_into(),
    }
});

mtry_from!('a, DefinedInfixFormula<'a>; |value| {
    let left: A = (*value.left).try_into()?;
    let right: A = (*value.right).try_into()?;
    Ok(A::new(
        EQUALITY.name().to_string(),
        vec![left, right]
    ))
});

mtry_from!('a, DefinedTerm<'a>; |value| {
    match value {
        DefinedTerm::Defined(d) => Ok(A::new_const(d.to_string())),
        DefinedTerm::Atomic(a) => a.try_into(),
    }
});

impl A {
    pub fn new<U, V>(head: U, args: implvec!(V)) -> Self
    where
        U: Into<String>,
        V: Into<TmpFormula>,
    {
        A(TmpFormula::new(head.into(), args.into_iter().map_into()))
    }

    pub fn new_const(head: String) -> Self {
        A(TmpFormula::new_const(head))
    }
}
