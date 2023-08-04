use std::{
    convert::Infallible,
    ops::{Deref, DerefMut},
};

use thiserror::Error;

#[inline(always)]
pub fn replace_if_eq<T: Eq>(a: T, b: T, c: T) -> T {
    if a == b {
        c
    } else {
        a
    }
}

pub fn clone_iter<'a, E, I>(iter: I) -> impl Iterator<Item = E> + 'a
where
    E: Clone + 'a,
    I: Iterator<Item = &'a E> + 'a,
{
    iter.map(|e| e.clone())
}

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

// pub(crate) fn reset_vec<'a, 'b, T>(v: &'a mut Vec<*const T>) -> &'a mut Vec<&'b T> {
//     v.clear();
//     unsafe { std::mem::transmute(v) }
// }

pub(crate) fn transpose<A: Eq + Clone, B: Eq>(vec: Vec<(A, Vec<B>)>) -> Vec<(B, Vec<A>)> {
    let mut result = vec![];

    for (a, v) in vec {
        for b in v {
            let i = result
                .iter()
                .position(|(b2, _)| b2 == &b)
                .unwrap_or_else(|| {
                    let i = result.len();
                    result.push((b, vec![]));
                    i
                });
            let bvec = &mut result[i].1;
            if !bvec.contains(&a) {
                bvec.push(a.clone())
            }
        }
    }
    result
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
macro_rules! implvec {
    ($t:ty) => {
        impl std::iter::IntoIterator<Item = $t>
    };

}

/// A macro to do pattern matching on any [IntoIterator]
///
/// # Example
///
/// Base usage
/// ```
/// # use automator::destvec;
/// let vec = vec![1,3,4];
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
/// # use automator::destvec;
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

    ([$($arg:ident),*] = $vec:expr; |$err:ident| $err_handling:block) => {
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
        if !iter.next().is_none() {
            {
                let $err = "too many elements";
                $err_handling ;
            }
        }
    }
}

/// Let's one use or pattern even when the bound variables don't share
/// a type by rewriting the block of code to each branch.
///
///
/// ```rust
/// use automator::match_as_trait;
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
///
/// ```
#[macro_export]
macro_rules! match_as_trait {
    ($e:expr => {$($($pat:pat_param)|+ => $b:block),*}) => {
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

/// sortcut for [std::fmt::format]
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

    #[must_use]
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

// pub trait LateInitializable: MaybeInvalid {
//     type Inner;

//     /// Replace the underlying function
//     ///
//     /// *Not thread safe*
//     unsafe fn inner_overwrite(&self, other: Self::Inner);

//     /// **DO NOT OVERWRITE THIS FUNCTION**
//     #[must_use]
//     unsafe fn initiallize(&self, other: Self::Inner) -> Result<&Self, AlreadyInitialized> {
//         if !self.is_valid() {
//             self.inner_overwrite(other);
//             Ok(self)
//         } else {
//             if cfg!(debug_assertions) {
//                 unreachable!("{}", AlreadyInitialized::default())
//             } else {
//                 Err(Default::default())
//             }
//         }
//     }
// }
