use std::marker::PhantomData;

use thiserror::Error;

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Error)]
#[error("conversion error (from {}, to {})", std::any::type_name::<From>(), std::any::type_name::<To>())]
pub struct ConversionError<From, To> {
    from: PhantomData<From>,
    to: PhantomData<To>,
}

impl<T, F> Default for ConversionError<F, T> {
    fn default() -> Self {
        Self {
            from: Default::default(),
            to: Default::default(),
        }
    }
}

pub trait VariantsUtils<V> {
    fn is_variant(&self) -> bool {
        self.ref_variant().is_some()
    }
    fn ref_variant(&self) -> Option<&V>;
    fn owned_variant(self) -> Option<V>;
}

#[macro_export]
macro_rules! variants {
    ($base:ty; $variant:ident : $t:ty) => {
        paste::paste! {
            pub fn [<as_ $variant:snake>](&self) -> ::core::option::Option<&$t> {
                match self {
                    $base::$variant(x) => ::core::option::Option::Some(x),
                    _ => ::core::option::Option::None
                }
            }
        }
        paste::paste! {
            pub fn [<is_ $variant:snake>](&self) -> bool {
                self.[<as_ $variant:snake>]().is_some()
            }
        }
    };
    ($base:ty; $($variant:ident: $t:ty),*) => {
        $(
            variants!($base; $variant : $t);
        )*
    };
    ($base:ty; $($variant:ident: $t:ty,)*) => {
        variants!($base; $($variant: $t),*);
    };
}

#[macro_export]
macro_rules! variants_ref {
    ($base:ty; $variant:ident : $t:ty) => {
        paste::paste! {
            pub fn [<as_ $variant:snake>](&self) -> ::core::option::Option<&$t> {
                match self.as_ref() {
                    $base::$variant(x) => ::core::option::Option::Some(x),
                    _ => ::core::option::Option::None
                }
            }
        }
        paste::paste! {
            pub fn [<is_ $variant:snake>](&self) -> bool {
                self.[<as_ $variant:snake>]().is_some()
            }
        }
    };
    ($base:ty; $($variant:ident: $t:ty),*) => {
        $(
            variants_ref!($base; $variant : $t);
        )*
    };
    ($base:ty; $($variant:ident: $t:ty,)*) => {
        variants_ref!($base; $($variant: $t),*);
    };

    ($base:ty, $lt:lifetime; $variant:ident : $t:ty) => {
        paste::paste! {
            pub fn [<precise_as_ $variant:snake>](&self) -> ::core::option::Option<&$lt $t> {
                match self.precise_as_ref() {
                    $base::$variant(x) => ::core::option::Option::Some(x),
                    _ => ::core::option::Option::None
                }
            }
        }

        paste::paste! {
            pub fn [<as_ $variant:snake>](&self) -> ::core::option::Option<&$t> {
                match self.precise_as_ref() {
                    $base::$variant(x) => ::core::option::Option::Some(x),
                    _ => ::core::option::Option::None
                }
            }
        }
        paste::paste! {
            pub fn [<is_ $variant:snake>](&self) -> bool {
                self.[<as_ $variant:snake>]().is_some()
            }
        }
    };
    ($base:ty, $lt:lifetime; $($variant:ident: $t:ty),*) => {
        $(
            variants_ref!($base, $lt; $variant : $t);
        )*
    };
    ($base:ty, $lt:lifetime; $($variant:ident: $t:ty,)*) => {
        variants_ref!($base, $lt; $($variant: $t),*);
    };
}

#[macro_export]
macro_rules! variants_ref_try_into {
    ($path:path:$from:ty => {$variant:ident :$to:ty}; $($other_lt:lifetime),*) => {
        impl<'ref_lt, $($other_lt),*> core::convert::TryInto<&'ref_lt $to> for &'ref_lt $from where $($other_lt : 'ref_lt),* {
            type Error = $crate::enum_utils::ConversionError<$from, $to>;

            fn try_into(self) -> Result<&'ref_lt $to, Self::Error> {
                match self {
                    paste::paste! { $path::$variant(x) }
                        => Ok(x),
                    _ => Err(std::default::Default::default())
                }
            }
        }
    };

    ($path:path: $from:ty => {$variant:ident: $to:ty | $($variants:ident: $tos:ty)|+}; $($other_lt:lifetime),+) => {
        variants_ref_try_into!($path:$from => {$variant:$to}; $($other_lt),*);
        variants_ref_try_into!($path:$from => {$($variants:$tos)|+}; $($other_lt),*);
    }
}

/// Static dispatch of iterators
#[macro_export]
macro_rules! dynamic_iter {
    ($name:ident; $($variant:ident:$t:ident),*) => {
        enum $name<$($t),*> {
            $(
                $variant($t)
            ),*
        }

        impl<T, $($t),*> ::std::iter::Iterator for $name<$($t),*>
        where $( $t: ::std::iter::Iterator<Item = T> ),* {
            type Item = T;

            fn next(&mut self) -> Option<T> {
                match self {
                    $(
                        Self::$variant(iter) => iter.next()
                    ),*
                }
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                match self {
                    $(
                        Self::$variant(iter) => iter.size_hint()
                    ),*
                }
            }
        }

        impl<$($t),*> ::std::iter::FusedIterator for $name<$($t),*>
        where
            Self: ::std::iter::Iterator,
            $( $t: ::std::iter::FusedIterator ),*
        {}

        impl<$($t),*> ::std::iter::ExactSizeIterator for $name<$($t),*>
        where
            Self: ::std::iter::Iterator,
            $( $t: ::std::iter::ExactSizeIterator ),*
        {}

        // impl<$($t),*> ::std::iter::DoubleEndedIterator for $name<$($t),*>
        // where
        //     Self: ::std::iter::Iterator,
        //     $( $t: ::std::iter::DoubleEndedIterator ),*
        // {
        //     fn next_back(&mut self) -> Option<Self::Item> {
        //         match self {
        //             $(
        //                 Self::$variant(iter) => iter.next_back()
        //             ),*
        //         }
        //     }
        // }
    };
}
