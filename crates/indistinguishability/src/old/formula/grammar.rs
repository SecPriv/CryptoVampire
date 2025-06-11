use std::fmt::write;

use anyhow::anyhow;
use egg::{Analysis, EGraph, FromOp, Id, Language, Var};
use itertools::Itertools;
use utils::{ereturn_if, implvec, iter_array::IntoArray};

use super::Variable;

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Hash)]
pub enum Name {
    Str(String),
}
impl core::fmt::Display for Name {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Name::Str(n) => write!(f, "{n}"),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Hash)]
pub struct Index(pub u32);

impl core::fmt::Display for Index {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "#{:}", self.0)
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Hash)]
pub enum Op {
    Var(Variable),
    Nonce,
    Name(Name),
    Index(Index),

    Enc,
    Dec,

    Hash,

    Eq,
    IfThenElse,

    Tuple,
    P1,
    P2,

    And,
    Or,
    Not,

    Length,

    Zeroes,

    Input,
    Equiv,

    Err,
}

impl Op {
    pub fn arity(&self) -> usize {
        use Op::*;
        match self {
            Var(_) => 0,
            Nonce => 1,
            Index(_) => 0,
            Enc => 3,
            Dec => 2,
            Hash => 1,
            Eq => 2,
            IfThenElse => 3,
            Tuple => 2,
            P1 => 1,
            P2 => 1,
            And => 2,
            Or => 2,
            Not => 1,
            Length => 1,
            Zeroes => 1,
            Input => 1,
            Equiv => 1,
            Err => 0,

            Name(name) => todo!(),
        }
    }

    /// Returns `true` if the op is [`Input`].
    ///
    /// [`Input`]: Op::Input
    #[must_use]
    pub fn is_input(&self) -> bool {
        matches!(self, Self::Input)
    }

    pub fn app<'a>(self, args: implvec!(&'a Id)) -> TA {
        let args = args.into_iter().copied().collect_vec();
        assert!(args.len() == self.arity());
        TA { op: self, args }
    }

    /// Returns `true` if the op is [`Equiv`].
    ///
    /// [`Equiv`]: Op::Equiv
    #[must_use]
    pub fn is_equiv(&self) -> bool {
        matches!(self, Self::Equiv)
    }

    /// Returns `true` if the op is [`Nonce`].
    ///
    /// [`Nonce`]: Op::Nonce
    #[must_use]
    pub fn is_nonce(&self) -> bool {
        matches!(self, Self::Nonce)
    }

    /// Returns `true` if the op is [`Name`].
    ///
    /// [`Name`]: Op::Name
    #[must_use]
    pub fn is_name(&self) -> bool {
        matches!(self, Self::Name(..))
    }
}

impl std::str::FromStr for Op {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> anyhow::Result<Self> {
        match s {
            "nonce" => Ok(Self::Nonce),
            "enc" => Ok(Self::Enc),
            "dec" => Ok(Self::Dec),
            "hash" => Ok(Self::Hash),
            "===" | "eq" => Ok(Self::Eq),
            "ite" | "if_then_else" => Ok(Self::IfThenElse),
            "tuple" | "tpl" => Ok(Self::Tuple),
            "p1" | "sel1of2" | "π₁" => Ok(Self::P1),
            "p2" | "sel2of2" | "π₂" => Ok(Self::P2),
            "and" | "&&" | "∧" | "/\\" => Ok(Self::And),
            "or" | "||" | "∨" | "\\/" => Ok(Self::Or),
            "neg" | "not" | "¬" => Ok(Self::Not),
            "length" | "len" => Ok(Self::Length),
            "zeroes" => Ok(Self::Zeroes),
            "input" => Ok(Self::Input),
            "equiv" => Ok(Self::Equiv),
            "err" => Ok(Self::Err),
            "" => Err(anyhow!("empty op")),
            x => x
                .split_at_checked(2)
                .and_then(|(det, x)| match det {
                    "_?" => Some(x.parse().map(Variable).map(Self::Var)),
                    "_#" => Some(x.parse().map(Index).map(Self::Index)),
                    _ => None,
                })
                .unwrap_or_else(|| Ok(Self::Name(Name::Str(x.into()))))
                .map_err(|e| e.into()),
        }
    }
}

impl core::fmt::Display for Op {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        use Op::*;
        match self {
            Var(variable) => variable.fmt(f),
            Nonce => write!(f, "nonce"),
            Name(name) => name.fmt(f),
            Index(index) => index.fmt(f),
            Enc => write!(f, "enc"),
            Dec => write!(f, "dec"),
            Hash => write!(f, "hash"),
            Eq => write!(f, "==="),
            IfThenElse => write!(f, "if_then_else"),
            Tuple => write!(f, "tuple"),
            P1 => write!(f, "π₁"),
            P2 => write!(f, "π₂"),
            And => write!(f, "∧"),
            Or => write!(f, "∨"),
            Not => write!(f, "¬"),
            Length => write!(f, "length"),
            Zeroes => write!(f, "zeroes"),
            Input => write!(f, "input"),
            Equiv => write!(f, "equiv"),
            Err => write!(f, "err"),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Hash)]
pub struct TA {
    op: Op,
    args: Vec<Id>,
}

impl std::ops::Deref for TA {
    type Target = Op;

    fn deref(&self) -> &Self::Target {
        &self.op
    }
}

impl TA {
    pub fn op(&self) -> &Op {
        &self.op
    }

    pub fn args_arr<const N: usize>(&self) -> Option<[Id; N]> {
        ereturn_if!(self.arity() != N, None);
        let (arr, mut x) = self.children().iter().copied().collect_array().unwrap();
        debug_assert!(x.next().is_none());
        Some(arr)
    }

    pub fn get_name<N: Analysis<TA>>(egraph: &EGraph<TA, N>, id: Id) -> Option<Id> {
        egraph[id]
            .iter()
            .filter_map(|l| l.is_nonce().then(|| l.children()[0]))
            .next()
    }
}

impl Language for TA {
    type Discriminant = Op;
    fn matches(&self, other: &Self) -> bool {
        self.op() == other.op() && self.arity() == other.arity()
    }

    fn children(&self) -> &[Id] {
        &self.args
    }

    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.args
    }

    fn discriminant(&self) -> Self::Discriminant {
        self.op().clone()
    }
}

impl FromOp for TA {
    type Error = anyhow::Error;

    fn from_op(op: &str, args: Vec<Id>) -> Result<Self, Self::Error> {
        let op: Op = op.parse()?;
        anyhow::ensure!(op.arity() == args.len(), "arity mishmatch");
        Ok(TA { op, args })
    }
}
impl core::fmt::Display for TA {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.op().fmt(f)
    }
}
