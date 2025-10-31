use core::hash::Hash;
use std::error::Error;
use std::fmt::{Debug, Display};
use std::str::FromStr;

use egg::{ENodeOrVar, FromOp, Id, Language, RecExpr, SymbolLang};
use itertools::Itertools;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use thiserror::Error;
use utils::implvec;
use utils::impossible::Impossible;

use crate::{Destructed, Formula, Head, head};
/// A trait for discriminants that can be used in `SimplLang`.
pub trait SimpleDiscriminant: Debug + Clone + Eq + Ord + Hash {
    /// Returns `true` if the discriminant is valid for the given children IDs.
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

    fn app_empty<const N: usize>(&self) -> RecExpr<SimplLang<Self, N>> {
        self.app::<N, [_; 0]>(&[])
    }

    fn app_var<const N: usize, E: AsRef<[SimplLangVar<Self, N>]>>(
        &self,
        ids: &[E],
    ) -> RecExpr<SimplLangVar<Self, N>> {
        let head = egg::ENodeOrVar::ENode(self.app_id((0..ids.len()).map(Id::from)));
        head.join_recexprs(|i| &ids[usize::from(i)])
    }

    fn app_empty_var<const N: usize>(&self) -> RecExpr<SimplLangVar<Self, N>> {
        self.app_var::<N, [_; 0]>(&[])
    }
}

/// A trait for converting an operation and its children into a language term.
pub trait FromOpGeneral<O>: egg::Language + Sized {
    /// The error type returned when conversion fails.
    type Error: std::fmt::Debug;

    /// Converts an operation and its children into a language term.
    fn from_op(op: O, children: Vec<egg::Id>) -> Result<Self, Self::Error>;
}

/// A simplified language for `egg` that uses a generic discriminant `D` and a fixed-size array for arguments.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SimplLang<D, const N: usize = 3> {
    pub head: D,
    pub args: SmallVec<[Id; N]>,
}
/// A type alias for `egg::ENodeOrVar` with `SimplLang`.
pub type SimplLangVar<D, const N: usize = 3> = egg::ENodeOrVar<SimplLang<D, N>>;

/// Errors that can occur when parsing `SimplLang`.
#[derive(Debug, Clone, Copy, Error)]
pub enum SimpleLangParseError<E: Error + Debug> {
    #[error("invalid arguments")]
    InValid,
    #[error(transparent)]
    ParseError(#[from] E),
}

impl<D: Display, const N: usize> Display for SimplLang<D, N> {
    /// Formats the `SimplLang` for display.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.head.fmt(f)
    }
}

impl<D: SimpleDiscriminant, const N: usize> Language for SimplLang<D, N> {
    /// The discriminant type for `SimplLang`.
    type Discriminant = D;

    /// Returns the discriminant of the `SimplLang` node.
    fn discriminant(&self) -> Self::Discriminant {
        self.head.clone()
    }

    /// Returns `true` if the two `SimplLang` nodes match.
    fn matches(&self, other: &Self) -> bool {
        self.head == other.head && self.args.len() == other.args.len()
    }

    /// Returns a slice of the children IDs.
    fn children(&self) -> &[Id] {
        &self.args
    }

    /// Returns a mutable slice of the children IDs.
    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.args
    }
}

impl<D: SimpleDiscriminant, const N: usize> SimplLang<D, N> {
    /// Creates a new `SimplLang` instance.
    pub fn new<I: IntoIterator<Item = Id>>(head: D, args: I) -> Self {
        Self {
            head,
            args: args.into_iter().collect(),
        }
    }

    /// Build a new [Self] but is `const`
    ///
    /// If `len < N` then the content of `args[len..]` is irrelevant
    ///
    /// ### panics
    /// if `len > N`.
    pub const fn new_const(head: D, args: [Id; N], len: usize) -> Self {
        assert!(len <= N);
        Self {
            head,
            // the assert ensure len <= N
            args: unsafe { SmallVec::from_const_with_len_unchecked(args, len) },
        }
    }

    /// Returns `true` if the `SimplLang` instance is valid.
    pub fn valid(&self) -> bool {
        let Self { head, args } = self;
        head.valid(args)
    }

    /// Converts a `SymbolLang` expression into a `RecExpr<SimplLang<D, N>>`.
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

    /// Converts a `SymbolLang` expression with variables into a `RecExpr<SimplLangVar<D, N>>`.
    pub fn from_var_symbollang<E: Error>(
        expr: &[egg::ENodeOrVar<SymbolLang>],
        mut convert: impl FnMut(&str) -> Result<D, E>,
    ) -> Result<RecExpr<SimplLangVar<D, N>>, SimpleLangParseError<E>> {
        let inner: Result<Vec<_>, SimpleLangParseError<_>> = expr
            .iter()
            .map(|f| match f {
                egg::ENodeOrVar::ENode(f) => {
                    let op = convert(f.op.as_str())?;
                    Ok(egg::ENodeOrVar::ENode(
                        FromOpGeneral::from_op(op, f.children.clone())
                            .map_err(|_: ()| SimpleLangParseError::InValid)?,
                    ))
                }
                egg::ENodeOrVar::Var(var) => Ok(egg::ENodeOrVar::Var(*var)),
            })
            .collect();
        Ok(RecExpr::from(inner?))
    }
}

impl<E: Error + Debug> SimpleLangParseError<E> {
    /// Maps the inner error type to another error type.
    pub fn map<E2: Error + Debug>(self, f: impl FnOnce(E) -> E2) -> SimpleLangParseError<E2> {
        match self {
            SimpleLangParseError::InValid => SimpleLangParseError::InValid,
            SimpleLangParseError::ParseError(e) => SimpleLangParseError::ParseError(f(e)),
        }
    }
}

impl<D: SimpleDiscriminant, const N: usize> FromOpGeneral<D> for SimplLang<D, N> {
    /// The error type returned when conversion fails.
    type Error = ();

    /// Converts a discriminant and its children into a `SimplLang` term.
    fn from_op(head: D, children: Vec<egg::Id>) -> Result<Self, Self::Error> {
        let res = Self {
            head,
            args: children.into(),
        };
        if res.valid() { Ok(res) } else { Err(()) }
    }
}

impl<D: SimpleDiscriminant + FromStr, const N: usize> FromOp for SimplLang<D, N>
where
    D::Err: Error + Debug,
{
    /// The error type returned when conversion fails.
    type Error = SimpleLangParseError<D::Err>;

    /// Converts an operation string and its children into a `SimplLang` term.
    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        let op: D = op.parse()?;
        match FromOpGeneral::from_op(op, children) {
            Ok(x) => Ok(x),
            Err(_) => Err(SimpleLangParseError::InValid),
        }
    }
}

impl<L: egg::FromOp> FromOpGeneral<&str> for L {
    /// The error type returned when conversion fails.
    type Error = <L as egg::FromOp>::Error;

    /// Converts an operation string and its children into a language term.
    fn from_op(op: &str, children: Vec<egg::Id>) -> Result<Self, Self::Error> {
        <L as egg::FromOp>::from_op(op, children)
    }
}

impl<F: egg::Language> Formula for &[egg::ENodeOrVar<F>] {
    /// The variable type for the formula.
    type Var = egg::Var;

    /// The function discriminant type for the formula.
    type Fun = F::Discriminant;

    /// The quantifier type for the formula.
    type Quant = Impossible;

    /// Destructures the formula into its head and arguments.
    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        let n = self.len();
        let head = self.last().expect("empty formula");
        let args = head
            .children()
            .iter()
            .map(move |i| &self[..=usize::from(*i)]);
        let head = match head {
            egg::ENodeOrVar::ENode(h) => Head::<Self>::Fun(h.discriminant()),
            egg::ENodeOrVar::Var(v) => Head::<Self>::Var(*v),
        };
        Destructed { head, args }
    }

    /// Returns an iterator over the used variables in the formula.
    fn used_vars_iter(self) -> impl Iterator<Item = Self::Var>
    where
        Self::Var: Eq + Clone,
    {
        self.iter().filter_map(|f| match f {
            ENodeOrVar::ENode(_) => None,
            ENodeOrVar::Var(v) => Some(*v),
        })
    }

    /// Returns an iterator over the free variables in the formula.
    fn free_vars_iter(self) -> impl Iterator<Item = Self::Var>
    where
        Self::Quant: crate::Bounder<Self::Var>,
        Self::Var: Eq + Clone,
    {
        self.used_vars_iter()
    }
}

impl<'a, D, const N: usize, I> From<Destructed<&'a [egg::ENodeOrVar<SimplLang<D, N>>], I>>
    for RecExpr<egg::ENodeOrVar<SimplLang<D, N>>>
where
    I: Iterator<Item = &'a [egg::ENodeOrVar<SimplLang<D, N>>]>,
    D: SimpleDiscriminant,
{
    /// Converts a `Destructed` instance into a `RecExpr`.
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
