mod error;
mod fixed_signature;
mod lazy_signature;
mod partial_signature;

pub use lazy_signature::Lazy;

pub use error::CheckError;
pub use fixed_signature::{FixedRefSignature, StaticSignature};
pub use partial_signature::{OnlyArgsSignature, OnlyArgsSignatureProxy};

use std::{fmt::Display, ops::RangeInclusive};

use itertools::{Itertools, MapInto};

use crate::{
    environement::traits::{KnowsRealm, Realm},
    formula::sort::{sort_proxy::SortProxy, Sort},
};
use utils::infinity::Infinity;

/// A very general trait of what should be a signature of a function
pub trait Signature<'bump>: Sized {
    /// [Iterator] over the argument's [SortProxy]. See [Self::args()]
    type Args<'a>: IntoIterator<Item = SortProxy<'bump>> + 'a
    where
        Self: 'a,
        'bump: 'a;

    type FxSign: AsFixedSignature<'bump>;

    /// output sort
    fn out(&self) -> SortProxy<'bump>;
    ///  [Iterator] over the argument's [SortProxy].
    ///
    /// This iterator may or may not be finite. The use of [SortProxy]
    /// takes polymorphism into account
    fn args<'a>(&'a self) -> Self::Args<'a>
    where
        'bump: 'a;

    /// Force a signature out when it is possible. Return [None] when
    /// this doesn't make sense
    fn fast(self) -> Option<Self::FxSign>;

    /// The number of arguments
    ///
    /// This should be compatible with [Self::Args::size_hint()]
    fn args_size(&self) -> RangeInclusive<Infinity<usize>>;

    /// Unifies `self` with `other`.
    ///
    /// The errors will be thrown out assuming `self` is the grounder truth
    fn unify<S, R>(&self, other: &S, env: &R) -> Result<(), CheckError<'bump>>
    where
        S: Signature<'bump>,
        R: KnowsRealm,
    {
        self.out()
            .unify(&other.out(), env)
            .map_err(|error| CheckError::SortError {
                position: None,
                error,
            })?;

        let args_unify = self
            .args()
            .into_iter()
            .zip_longest(other.args().into_iter())
            .enumerate()
            .try_fold(None, |_, (i, e)| match e {
                itertools::EitherOrBoth::Both(l, r) => l
                    .unify(&r, env)
                    .map_err(|e| CheckError::from_inference(e, Some(i)))
                    .map(|_| None),
                itertools::EitherOrBoth::Left(_) => Err(CheckError::WrongNumberOfArguments {
                    got: i.into(),
                    expected: self.args_size(),
                }),
                itertools::EitherOrBoth::Right(_) => Ok(Some(i)),
            })?;

        match args_unify {
            Some(i) => Err(CheckError::WrongNumberOfArguments {
                got: i.into(),
                expected: self.args_size(),
            }),
            None => Ok(()),
        }
    }

    /// To not force implement [Display]
    fn as_display(&'_ self) -> DisplaySignature<'_, Self> {
        DisplaySignature(self)
    }

    /// The [Realm] in which this function should be used. [None] if it doesn't matter or can't be decided
    fn realm(&self) -> Option<Realm> {
        self.out().as_option().and_then(|s| s.realm())
    }
}

/// Shortcut to get to the [Iterator] hidden in [Signature::Args]
#[allow(dead_code)]
type SignatureArgs<'a, 'bump, T> = <<T as Signature<'bump>>::Args<'a> as IntoIterator>::IntoIter;

pub trait AsFixedSignature<'bump> {
    type Args<'a>: IntoIterator<Item = Sort<'bump>> + 'a
    where
        Self: 'a,
        'bump: 'a;

    fn fixed_out(&self) -> Sort<'bump>;
    fn fixed_args<'a>(&'a self) -> Self::Args<'a>
    where
        'bump: 'a;
}

/// Shortcut to get to the [Iterator] hidden in [FixedSignature::Args]
type FixedSignatureArgs<'a, 'bump, T> =
    <<T as AsFixedSignature<'bump>>::Args<'a> as IntoIterator>::IntoIter;

impl<'bump, T> Signature<'bump> for T
where
    T: Sized + AsFixedSignature<'bump>,
{
    // type Args<'a> = MapInto<<<Self as FixedSignature<'bump>>::Args<'a>  as IntoIterator>::IntoIter ,SortProxy<'bump>>
    type Args<'a> = MapInto<FixedSignatureArgs<'a, 'bump, Self> ,SortProxy<'bump>>
    where
        Self: 'a, 'bump:'a;

    type FxSign = Self;

    fn out(&self) -> SortProxy<'bump> {
        self.fixed_out().into()
    }

    fn args<'a>(&'a self) -> Self::Args<'a>
    where
        'bump: 'a,
    {
        self.fixed_args().into_iter().map_into()
    }

    fn fast(self) -> Option<Self::FxSign> {
        Some(self)
    }

    fn args_size(&self) -> RangeInclusive<Infinity<usize>> {
        let len = self.args().count();
        len.into()..=len.into()
    }
}

/// A bottom type, to define [Signature::fast] when it always return [None]
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Impossible {}

impl<'bump> AsFixedSignature<'bump> for Impossible {
    type Args<'a> = std::iter::Empty<Sort<'bump>>
    where Self:'a, 'bump:'a;

    fn fixed_out(&self) -> Sort<'bump> {
        unreachable!()
    }

    fn fixed_args<'a>(&'a self) -> Self::Args<'a>
    where
        'bump: 'a,
    {
        unreachable!()
    }
}

pub struct DisplaySignature<'a, T>(&'a T);

impl<'a, 'bump: 'a, T: Signature<'bump>> Display for DisplaySignature<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let DisplaySignature(s) = self;

        let args = s.args().into_iter().join(",");
        let out = s.out();
        write!(f, "({args}) -> {out}")
    }
}

impl<'a, 'bump: 'a, T: Signature<'bump>> From<&'a T> for DisplaySignature<'a, T> {
    fn from(value: &'a T) -> Self {
        DisplaySignature(value)
    }
}
