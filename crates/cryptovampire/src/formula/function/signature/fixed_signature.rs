use std::fmt::Display;
use std::iter::Cloned;
use std::slice::Iter;

use utils::vecref::VecRefClone;

use super::{AsFixedSignature, Signature};
use crate::formula::sort::Sort;

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

impl<'a, 'bump> FixedRefSignature<'a, 'bump>
where
    'bump: 'a,
{
    pub fn new<I>(out: Sort<'bump>, args: I) -> Self
    where
        I: Into<VecRefClone<'a, Sort<'bump>>>,
    {
        Self {
            out,
            args: args.into(),
        }
    }
}

impl<'a, 'bump: 'a> AsFixedSignature<'bump> for FixedRefSignature<'a, 'bump> {
    type Args<'b>
        = Cloned<<&'b VecRefClone<'a, Sort<'bump>> as IntoIterator>::IntoIter>
    where
        Self: 'b,
        'bump: 'a;

    fn fixed_out(&self) -> Sort<'bump> {
        self.out
    }

    fn fixed_args<'b>(&'b self) -> Self::Args<'b>
    where
        'bump: 'b,
    {
        (&self.args).into_iter().cloned()
    }
}

impl<'a, 'bump: 'a, const N: usize> From<&'a StaticSignature<'bump, N>>
    for FixedRefSignature<'a, 'bump>
{
    fn from(value: &'a StaticSignature<'bump, N>) -> Self {
        FixedRefSignature {
            out: value.out,
            args: (&value.args).into(),
        }
    }
}

impl<'a, 'bump: 'a> Display for FixedRefSignature<'a, 'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_display().fmt(f)
    }
}

/// Same as [FixedRefSignature] but `'static`
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct StaticSignature<'bump, const N: usize> {
    pub out: Sort<'bump>,
    pub args: [Sort<'bump>; N],
}

impl<'bump, const N: usize> StaticSignature<'bump, N> {
    pub fn as_ref(&self) -> FixedRefSignature<'_, 'bump> {
        self.into()
    }
}

impl<'bump, const N: usize> AsFixedSignature<'bump> for StaticSignature<'bump, N> {
    type Args<'a>
        = Cloned<Iter<'a, Sort<'bump>>>
    where
        Self: 'a,
        'bump: 'a;

    fn fixed_out(&self) -> Sort<'bump> {
        self.out
    }

    fn fixed_args<'a>(&'a self) -> Self::Args<'a>
    where
        'bump: 'a,
    {
        self.args.iter().cloned()
    }
}

impl<'bump, const N: usize> Display for StaticSignature<'bump, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_display().fmt(f)
    }
}

/// To quickly define static signatures
#[macro_export]
macro_rules! static_signature {
    (($($arg:expr),*) -> $out:expr) => {
        $crate::formula::function::signature::StaticSignature {
            out: $out.as_sort(),
            args:  [$($arg.as_sort()),*]
        }
    };

    ($(($pub:tt))? $name:ident: ($($arg:expr),*) -> $out:expr) => {
    paste::paste!{
        const [<$name _ARGS_LEN>] : usize = $crate::static_signature!(@inner ($($arg,)*));
    }

    #[static_init::dynamic] #[allow(dead_code)]
    $($pub)? static $name: $crate::formula::function::signature::StaticSignature<'static, paste::paste!{ [<$name _ARGS_LEN>] }> =
        static_signature!(($($arg),*) -> $out);
    };

    (@inner ()) => { 0 };
    (@inner ($t:tt, $($other:tt,)*)) => { 1 + $crate::static_signature!(@inner ($($other,)*))};

}
