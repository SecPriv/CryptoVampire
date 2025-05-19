use core::hash::Hash;
use egg::{FromOp, Id, Language, RecExpr, SymbolLang};
use itertools::Itertools;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::{
    error::Error,
    fmt::{Debug, Display},
    str::FromStr,
};
use thiserror::Error;
use utils::{implvec, impossible::Impossible};

use crate::{head, Destructed, Formula, Head};
pub trait SimpleDiscriminant: Debug + Clone + Eq + Ord + Hash {
    fn valid(&self, _ids: &[Id]) -> bool {
        true
    }

    /// Builds a [SimplLang]. Panics if not valid
    fn app_id<const N: usize>(&self, ids: implvec!(Id)) -> SimplLang<Self, N> {
        let res = SimplLang::new(self.clone(), ids);
        assert!(res.valid());
        res
    }

    fn app<const N: usize, E: AsRef<[SimplLang<Self, N>]>>(
        &self,
        ids: &[E],
    ) -> RecExpr<SimplLang<Self, N>> {
        let head = self.app_id((0..ids.len()).map(Id::from));
        head.join_recexprs(|i| &ids[usize::from(i)])
    }

    fn app_var<const N: usize, E: AsRef<[SimplLangVar<Self, N>]>>(
        &self,
        ids: &[E],
    ) -> RecExpr<SimplLangVar<Self, N>> {
        let head = egg::ENodeOrVar::ENode(self.app_id((0..ids.len()).map(Id::from)));
        head.join_recexprs(|i| &ids[usize::from(i)])
    }
}

pub trait FromOpGeneral<O>: egg::Language + Sized {
    type Error: std::fmt::Debug;

    fn from_op(op: O, children: Vec<egg::Id>) -> Result<Self, Self::Error>;
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SimplLang<D, const N: usize = 3> {
    head: D,
    args: SmallVec<[Id; N]>,
}
pub type SimplLangVar<D, const N: usize = 3> = egg::ENodeOrVar<SimplLang<D, N>>;

#[derive(Debug, Clone, Copy, Error)]
pub enum SimpleLangParseError<E: Error + Debug> {
    #[error("invalid arguments")]
    InValid,
    #[error(transparent)]
    ParseError(#[from] E),
}

impl<D: Display, const N: usize> Display for SimplLang<D, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.head.fmt(f)
    }
}

impl<D: SimpleDiscriminant, const N: usize> Language for SimplLang<D, N> {
    type Discriminant = D;

    fn discriminant(&self) -> Self::Discriminant {
        self.head.clone()
    }

    fn matches(&self, other: &Self) -> bool {
        self.head == other.head && self.args.len() == other.args.len()
    }

    fn children(&self) -> &[Id] {
        &self.args
    }

    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.args
    }
}

impl<D: SimpleDiscriminant, const N: usize> SimplLang<D, N> {
    pub fn new<I: IntoIterator<Item = Id>>(head: D, args: I) -> Self {
        Self {
            head,
            args: args.into_iter().collect(),
        }
    }

    pub fn valid(&self) -> bool {
        let Self { head, args } = self;
        head.valid(args)
    }

    pub fn from_symbollang<E: Error>(
        expr: &[SymbolLang],
        mut convert: impl FnMut(&str) -> Result<D, E>,
    ) -> Result<RecExpr<SimplLang<D, N>>, SimpleLangParseError<E>> {
        let inner: Result<Vec<_>, SimpleLangParseError<_>> = expr
            .iter()
            .map(|f| {
                let op = convert(f.op.as_str())?;
                FromOpGeneral::from_op(op, f.children.clone())
                    .map_err(|_: ()| SimpleLangParseError::InValid)
            })
            .collect();
        Ok(RecExpr::from(inner?))
    }

    pub fn from_var_symbollang<E: Error>(
        expr: &[egg::ENodeOrVar<SymbolLang>],
        mut convert: impl FnMut(&str) -> Result<D, E>,
    ) -> Result<RecExpr<SimplLangVar<D, N>>, SimpleLangParseError<E>> {
        let inner: Result<Vec<_>, SimpleLangParseError<_>> = expr
            .iter()
            .map(|f| match f {
                egg::ENodeOrVar::ENode(f) => {
                    let op = convert(f.op.as_str())?;
                    Ok(egg::ENodeOrVar::ENode(FromOpGeneral::from_op(op, f.children.clone())
                        .map_err(|_: ()| SimpleLangParseError::InValid)?))
                }
                egg::ENodeOrVar::Var(var) => Ok(egg::ENodeOrVar::Var(*var)),
            })
            .collect();
        Ok(RecExpr::from(inner?))
    }
}

impl<E: Error + Debug> SimpleLangParseError<E> {
    pub fn map<E2: Error + Debug>(self, f: impl FnOnce(E) -> E2) -> SimpleLangParseError<E2> {
        match self {
            SimpleLangParseError::InValid => SimpleLangParseError::InValid,
            SimpleLangParseError::ParseError(e) => SimpleLangParseError::ParseError(f(e)),
        }
    }
}

impl<D: SimpleDiscriminant, const N: usize> FromOpGeneral<D> for SimplLang<D, N> {
    type Error = ();

    fn from_op(head: D, children: Vec<egg::Id>) -> Result<Self, Self::Error> {
        let res = Self {
            head,
            args: children.into(),
        };
        if res.valid() {
            Ok(res)
        } else {
            Err(())
        }
    }
}

impl<D: SimpleDiscriminant + FromStr, const N: usize> FromOp for SimplLang<D, N>
where
    D::Err: Error + Debug,
{
    type Error = SimpleLangParseError<D::Err>;

    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        let op: D = op.parse()?;
        match FromOpGeneral::from_op(op, children) {
            Ok(x) => Ok(x),
            Err(_) => Err(SimpleLangParseError::InValid),
        }
    }
}

impl<L: egg::FromOp> FromOpGeneral<&str> for L {
    type Error = <L as egg::FromOp>::Error;

    fn from_op(op: &str, children: Vec<egg::Id>) -> Result<Self, Self::Error> {
        <L as egg::FromOp>::from_op(op, children)
    }
}

impl<F: egg::Language> Formula for &[egg::ENodeOrVar<F>] {
    type Var = egg::Var;

    type Fun = F::Discriminant;

    type Quant = Impossible;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        let n = self.len();
        let head = self.first().expect("empty formula");
        let args = head
            .children()
            .iter()
            .map(move |i| &self[usize::from(*i)..n]);
        let head = match head {
            egg::ENodeOrVar::ENode(h) => Head::<Self>::Fun(h.discriminant()),
            egg::ENodeOrVar::Var(v) => Head::<Self>::Var(*v),
        };
        Destructed { head, args }
    }
}

impl<'a, D, const N: usize, I> From<Destructed<&'a [egg::ENodeOrVar<SimplLang<D, N>>], I>>
    for RecExpr<egg::ENodeOrVar<SimplLang<D, N>>>
where
    I: Iterator<Item = &'a [egg::ENodeOrVar<SimplLang<D, N>>]>,
    D: SimpleDiscriminant,
{
    fn from(
        Destructed { head, args }: Destructed<&'a [egg::ENodeOrVar<SimplLang<D, N>>], I>,
    ) -> Self {
        match head {
            head::HeadSk::Var(v) => [egg::ENodeOrVar::Var(v)].into_iter().collect(),
            head::HeadSk::Fun(f) => {
                let args: Vec<_> = args.collect();
                let head = SimplLang::new(f, (0..args.len()).map_into());
                egg::ENodeOrVar::ENode(head).join_recexprs(|id| &args[usize::from(id)])
            }
            head::HeadSk::Quant(_) => unreachable!(),
        }
    }
}
