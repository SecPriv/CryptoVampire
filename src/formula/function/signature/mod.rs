mod error;
mod fixed_signature;

pub use error::CheckError;
pub use fixed_signature::{FixedRefSignature, StaticSignature};

use std::{fmt::Display, ops::RangeInclusive};

use itertools::{Itertools, MapInto};

use crate::{
    formula::sort::{sort_proxy::SortProxy, Sort},
    utils::infinity::Infinity,
};

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
    ///
    /// *NB*: The blanket implementation assumes [Self::args()] is finite!
    /// Make sure to overwrite when this cannot be enforced
    fn fast(self) -> Option<Self::FxSign>;

    /// The number of arguments
    ///
    /// This should be compatible with [Self::Args::size_hint()]
    fn args_size(&self) -> RangeInclusive<Infinity<usize>>;

    fn unify<S: Signature<'bump>>(&self, other: &S) -> Result<(), CheckError<'bump>> {
        match self.out().unify(&other.out()) {
            Err(ie) => Err(CheckError::SortError {
                position: None,
                error: ie,
            }),
            Ok(_) => Ok(()),
        }?;

        // Itertools::zip_longest(self.args().into_iter(), other.args()).try_for_each(|e| match e {})
        Ok(())
    }

    /// To not force implement [Display]
    fn as_display(&'_ self) -> DisplaySignature<'_, Self> {
        DisplaySignature(self)
    }
}

/// Shortcut to get to the [Iterator] hidden in [Signature::Args]
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

// paste::paste!();

// To quickly define static signatures
// #[macro_export]
// macro_rules! static_signature {

//     ($name:ident: ($($arg:expr),*) -> $out:expr) => {
//     paste::paste!{
//         #[static_init::dynamic]
//         static  [<$name _ARGS>] : [$crate::formula::sort::Sort<'static>; $crate::static_signature!(@inner ($($arg,)*))]
//             = [$($arg.as_sort()),*];
//     }

//     #[static_init::dynamic]
//     static $name: $crate::formula::function::signature::FixedRefSignature<'static, 'static> =
//         $crate::formula::function::signature::FixedRefSignature {
//             out: $out.as_sort(),
//             args:  std::convert::From::from( paste::paste!{ [<$name _ARGS>] }.as_ref())
//         };
//     };

//     (@inner ()) => { 0 };
//     (@inner ($t:tt, $($other:tt,)*)) => { 1 + $crate::static_signature!(@inner ($($other,)*))};

// }
