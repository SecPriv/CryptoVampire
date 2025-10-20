use std::convert::Infallible;
use std::ops::{Deref, DerefMut};

use thiserror::Error;

#[inline(always)]
pub fn replace_if_eq<T: Eq>(a: T, b: T, c: T) -> T {
    if a == b { c } else { a }
}

/// A box that points to the stack,
///
/// This is mostly used to trick the type system when using [DerefMut]
pub struct StackBox<T>(T);

impl<T> StackBox<T> {
    pub fn new(t: T) -> Self {
        StackBox(t)
    }
}

impl<T> Deref for StackBox<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for StackBox<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
pub fn repeat_n_zip<P, I, T>(p: P, iter: I) -> impl Iterator<Item = (P, T)>
where
    P: Clone,
    I: IntoIterator<Item = T>,
{
    // std::iter::repeat(p).zip(iter.into_iter())
    iter.into_iter().map(move |t| (p.clone(), t))
}

#[macro_export]
macro_rules! implderef {
    ($b:lifetime, $t:ty) => {
        impl core::ops::Deref<Target = $t> + $b
    };
    ($t:ty) => {
        impl core::ops::Deref<Target = $t>
    };
}

#[macro_export]
/// Alias for arguments that take any list-like object
///
/// ```rust
/// use utils::implvec;
///
/// fn foo<'a>(arg: implvec!(&'a u8)) -> Vec<&'a u8> {
///     arg.into_iter().collect()
/// }
///
/// fn main() {
///     assert_eq!(vec![&1, &2], foo(&[1, 2]));
///     assert_eq!(vec![&1, &2], foo(&vec![1, 2]));
/// }
/// ```
macro_rules! implvec {
    ($t:ty) => {
        impl std::iter::IntoIterator<Item = $t>
    };
    ($t:ty : $lt:lifetime) => {
        impl std::iter::IntoIterator<Item = $t> + $tl
    };

}

/// A macro to do pattern matching on any [IntoIterator]
///
/// # Example
///
/// Base usage
/// ```
/// # use utils::destvec;
/// let vec = vec![1, 3, 4];
///
/// destvec!([a, b, c] = vec);
///
/// assert_eq!(a, 1);
/// assert_eq!(b, 3);
/// assert_eq!(c, 4);
/// ```
///
/// It is also possible to control what happens on failure with the second pattern
///
///
/// ```
/// # use utils::destvec;
/// let vec = vec![1,3,4,5];
///
/// destvec!([a, b, c] = vec; |err| { println!("{}",err); 0 });
///
/// assert_eq!(a, 1);
/// assert_eq!(b, 3);
/// assert_eq!(c, 4);
/// ```
#[macro_export]
macro_rules! destvec {
    ([$($arg:ident),*] = $vec:expr) => {
        destvec!{ [$($arg),*] = $vec; |err| {
            panic!("{}", err);
        }}
    };

    ([$($arg:ident),*,..$leftover:ident] = $vec:expr) => {
        destvec!{ [$($arg),*,..$leftover] = $vec; |err| {
            panic!("{}", err);
        }}
    };

    ([$($arg:ident),*] = $vec:expr; |$err:ident| $err_handling:block) => {
        destvec!{  [$($arg),*,.. leftover] = $vec; |$err| $err_handling }
        if !leftover.next().is_none() {
            {
                let $err = "too many elements";
                $err_handling ;
            }
        }
    };

    ([$($arg:ident),*,..$leftover:ident] = $vec:expr; |$err:ident| $err_handling:block) => {
        let mut iter = $vec.into_iter();
        $(
            let $arg = if let Some(tmp) = iter.next() {
                tmp
            } else {
                {
                    let $err = "not enough elements";
                    $err_handling
                }
            };
        )*

        let mut $leftover = iter;
    }
}

/// Let's one use or pattern even when the bound variables don't share
/// a type by rewriting the block of code to each branch.
///
///
/// ```rust
/// use utils::match_as_trait;
///
/// #[derive(Debug)]
/// struct A;
///
/// #[derive(Debug)]
/// struct B;
///
/// enum AB {A(A), B(B)}
///
/// fn printAB(ab:AB) {
///     match_as_trait!(ab => {AB::A(x) | AB::B(x) => {println!("{x:?}")}})
/// }
///
/// // is the same as
/// fn printABbis(ab:AB) {
///     match ab {
///         AB::A(x) => println!("{x:?}"),
///         AB::B(x) => println!("{x:?}"),
///     }
/// }
/// ```
#[macro_export]
macro_rules! match_as_trait {
    ($e:expr => {$($($pat:pat_param)|+ => $b:block),*$(,)?} ) => {
        match $e {
            $(
                $(
                    $pat => $b
                ),+
            )*
        }
    };
    ($t:path, |$x:ident| in $e:expr => $($variant:ident)|* $b:block) => {
        paste::paste! {
            match $e {
                $(
                    $t::$variant($x) => $b,
                )*
            }
        }
    }
}

#[macro_export]
macro_rules! match_eq {
    ($e:expr =>{$($($pat:ident)|+ => $b:block,)* _ => $base:block} ) => {

        if false {
            unreachable!()
        }
        $(
            else if $($e == &$pat ||)+ false {
                $b
            }
        )*  else {
            $base
        }
    };
}

/// shortcut for [std::fmt::format]
#[macro_export]
macro_rules! f {
    ($lit:literal $(, $arg:expr)*) => {format!($lit $(,$arg)*)};
    ($lit:literal $(, $arg:expr)*,) => {format!($lit $(,$arg)*)};
}

/// For things that might be invalid
///
/// # Reason
/// Many object cannot be soundly built in one go. Most notably some
/// [Function][crate::formula::function::Function] self recursive, and
/// [MemoryCell][crate::problem::cell::MemoryCell] needs to have its
/// [Assignement][crate::problem::cell::Assignement] built incrementally.
///
/// This trait is here to check if those object are properly initiallized
/// and propagate this notion to object that might sort them.
///
/// Maybe one day this could be replaced by [MaybeUninit][std::mem::MaybeUninit].
pub trait MaybeInvalid {
    fn is_valid(&self) -> bool;

    fn assert_valid(&self) -> Result<(), AccessToInvalidData> {
        if !self.is_valid() {
            if cfg!(debug_assertions) {
                unreachable!("{}", AccessToInvalidData::Error)
            } else {
                Err(AccessToInvalidData::Error)
            }
        } else {
            Ok(())
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Error, Default)]
pub enum AccessToInvalidData {
    #[error("Access to invalid data")]
    #[default]
    Error,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Error, Default)]
pub enum AlreadyInitialized {
    #[error("Overwritting already initialized data")]
    #[default]
    Error,
}

impl From<Infallible> for AlreadyInitialized {
    fn from(_value: Infallible) -> Self {
        unreachable!()
    }
}

pub fn print_type<T>(_: &T) -> &'static str {
    std::any::type_name::<T>()
}

#[macro_export]
macro_rules! try_trace {
    ($($t:tt)*) => {
        if log::log_enabled!(log::Level::Trace) {
            std::panic::catch_unwind(|| {
                log::trace!($($t)*);
            }).unwrap_or_else(|_|{
                log::trace!("error while printing");
            })
        }
    };
}

#[macro_export]
macro_rules! or_chain {
    ($b0:block) => {$crate::or_chain!($b0,)};
    ($b0:block,  $($b:block),*,) => {$crate::or_chain!($b0,$($b),*)};

    ($b0:block,  $($b:block),*) => {
        $b0$(.or_else(|| $b))*
    };
}
