#[cfg(test)]
pub mod tests {

    fn is_sync<T: Sync>() -> bool {
        true
    }
    fn is_send<T: Send>() -> bool {
        true
    }
}

/// makes sure traits are implemented
#[macro_export]
macro_rules! asssert_trait {
    ($name:ident; $to_test:ty; $($trait:ty),*) => {
        ::paste::paste! {
            #[cfg(test)]
            fn [<_$name:snake>]() {
                $(
                fn [<is_$trait:snake>]<T: $trait>() {}
                )*
                $([<is_$trait:snake>]::<$to_test>();)*
            }
        }
    };
}

/// make sure a type is covariant. [read more](https://doc.rust-lang.org/reference/subtyping.html)
#[macro_export]
macro_rules! assert_variance {
    ($name:ident) => {
        ::paste::paste! {
            #[cfg(test)]
            fn [<_enlarge_$name:snake>]<'long, 'short>(q: $name<'long>) -> $name<'short> where 'long:'short { q }
        }
    };
}

#[macro_export]
macro_rules! force_lifetime {
    ($t:ident, $long:lifetime) => {
        #[allow(dead_code)]
        pub fn shorten_lifetime<'short>(&self) -> &$t<'short>  where $long:'short { self }
    };
}