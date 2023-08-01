use std::{
    iter::{Cloned, Map},
    slice::Iter,
};

use itertools::{Either, Itertools, MapInto};
// use paste::paste;
use thiserror::Error;

use crate::{
    formula::{
        formula::RichFormula,
        sort::{
            sort_proxy::{self, InferenceError, SortProxy},
            Sort,
        },
    },
    implvec,
    utils::vecref::{IterVecRef, IterVecRefClone, VecRef, VecRefClone},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Error)]
pub enum CheckError<'bump> {
    #[error("wrong number of arguments (got {got}, expected {expected})")]
    WrongNumberOfArguments { got: usize, expected: usize },
    #[error("unsolvable sort problem at position {position:?}, caused by {error}")]
    SortError {
        position: Option<usize>,
        error: InferenceError<'bump>,
    },
}

/// A very general trait of what should be a signature of a function
pub trait Signature<'bump>: Sized {
    /// [Iterator] over the argument's [SortProxy]. See [Self::args()]
    type I<'a>: IntoIterator<Item = SortProxy<'bump>> + 'a
    where
        Self: 'a;

    /// output sort
    fn out(&self) -> SortProxy<'bump>;
    ///  [Iterator] over the argument's [SortProxy].
    ///
    /// This iterator may or may not be finite. The use of [SortProxy]
    /// takes polymorphism into account
    fn args(&'_ self) -> Self::I<'_>;

    /// Force a signature out when it is possible. Return [None] when
    /// this doesn't make sense
    ///
    /// *NB*: The blanket implementation assumes [Self::args()] is finite!
    /// Make sure to overwrite when this cannot be enforced
    fn fast(self) -> Option<FixedSignature<'bump>> {
        let out = self.out().as_option()?;
        let args: Option<Vec<Sort<'bump>>> = self.args().into_iter().map_into().collect();
        let args = args?;

        Some(FixedSignature { out, args })
    }

    /// Check if a [PartialImplSignature] can unify with [Self]
    fn check<J>(&self, sign: PartialImplSignature<'bump, J>) -> Result<bool, CheckError<'bump>>
    where
        J: IntoIterator<Item = Option<Sort<'bump>>>;

    /// Cheks is a list of argument can typecheck with this function
    fn check_rich_formulas<'a>(
        &self,
        args: implvec!(&'a RichFormula<'bump>),
    ) -> Result<(), CheckError<'bump>>
    where
        'bump: 'a,
    {
        self.check(PartialImplSignature {
            out: None,
            args: args.into_iter().map(|f| f.sort()),
        })
        .map(|_| ())
    }
}

/// when [Signature::fast()] always returns [Some]
pub trait FastSignature<'bump>: Signature<'bump> {
    fn faster(self) -> FixedSignature<'bump> {
        let fast = self.fast();
        debug_assert!(fast.is_some());
        unsafe { fast.unwrap_unchecked() }
    }
}

/// Owned fixed signature
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct FixedSignature<'bump> {
    pub out: Sort<'bump>,
    pub args: Vec<Sort<'bump>>,
}

impl<'bump> Signature<'bump> for FixedSignature<'bump> {
    type I<'a> = MapInto<Iter<'a, Sort<'bump>>, SortProxy<'bump>>  where Self:'a;

    fn out(&self) -> SortProxy<'bump> {
        self.out.into()
    }

    fn args(&'_ self) -> Self::I<'_> {
        self.args.iter().map_into()
    }

    fn fast(self) -> Option<FixedSignature<'bump>> {
        Some(self)
    }

    fn check<J>(&self, sign: PartialImplSignature<'bump, J>) -> Result<bool, CheckError<'bump>>
    where
        J: IntoIterator<Item = Option<Sort<'bump>>>,
    {
        let PartialImplSignature { out, args } = sign;

        let out = match out.map(|o| self.out().matches(o)).transpose() {
            Err(e) => Err(CheckError::SortError {
                position: None,
                error: e,
            }),
            Ok(o) => Ok(o.is_some()),
        }?;

        let args = self.args.iter().zip_longest(args).enumerate().try_fold(
            Either::Left(out),
            |acc, (i, c)| match c {
                itertools::EitherOrBoth::Both(es, ps) => {
                    match ps.map(|o| SortProxy::matches_sort(*es, o)).transpose() {
                        Err(error) => Err(CheckError::SortError {
                            position: Some(i),
                            error,
                        }),
                        Ok(x) => Ok(acc.map_left(|a| a && x.is_some())),
                    }
                }
                itertools::EitherOrBoth::Left(_) => Err(CheckError::WrongNumberOfArguments {
                    got: i,
                    expected: self.args.len(),
                }),
                itertools::EitherOrBoth::Right(_) => Ok(Either::Right(i)),
            },
        )?;
        match args {
            Either::Left(b) => Ok(b),
            Either::Right(i) => Err(CheckError::WrongNumberOfArguments {
                got: i,
                expected: self.args.len(),
            }),
        }
    }
}

impl<'bump> FastSignature<'bump> for FixedSignature<'bump> {}

/// a half finished signature
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct PartialImplSignature<'bump, I>
where
    I: IntoIterator<Item = Option<Sort<'bump>>>,
{
    pub out: Option<Sort<'bump>>,
    pub args: I,
}

/// A [Signature] that may of may not own its argument sort via the
/// use of [VecRefClone]
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct FixedRefSignature<'a, 'bump>
where
    'bump: 'a,
{
    pub out: Sort<'bump>,
    pub args: VecRefClone<'a, Sort<'bump>>,
}

impl<'a, 'bump: 'a> Signature<'bump> for FixedRefSignature<'a, 'bump> {
    type I<'b> = MapInto< IterVecRef<'b, 'b, Sort<'bump>>, SortProxy<'bump>>
    where
        Self: 'b, 'a:'b;

    fn out(&self) -> SortProxy<'bump> {
        self.out.into()
    }

    fn args(&'_ self) -> Self::I<'_> {
        self.args.iter().map_into()
    }

    fn check<J>(&self, sign: PartialImplSignature<'bump, J>) -> Result<bool, CheckError<'bump>>
    where
        J: IntoIterator<Item = Option<Sort<'bump>>>,
    {
        self.clone().faster().check(sign)
    }
}

impl<'a, 'bump: 'a> FastSignature<'bump> for FixedRefSignature<'a, 'bump> {}

paste::paste!();

#[macro_export]
macro_rules! static_signature {

    ($name:ident: ($($arg:expr),*) -> $out:expr) => {
    paste::paste!{
        #[static_init::dynamic]
        static  [<$name _ARGS>] : [$crate::formula::sort::Sort<'static>; $crate::static_signature!(@inner ($($arg,)*))]
            = [$($arg.as_sort()),*];
    }

    #[static_init::dynamic]
    static $name: $crate::formula::function::signature::FixedRefSignature<'static, 'static> =
        $crate::formula::function::signature::FixedRefSignature {
            out: $out.as_sort(),
            args:  std::convert::From::from( paste::paste!{ [<$name _ARGS>] }.as_ref())
        };
    };

    (@inner ()) => { 0 };
    (@inner ($t:tt, $($other:tt,)*)) => { 1 + $crate::static_signature!(@inner ($($other,)*))};

}
