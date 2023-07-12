#[cfg(test)]
pub mod tests {

    fn is_sync<T: Sync>() -> bool {
        true
    }
    fn is_send<T: Send>() -> bool {
        true
    }
}

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

#[macro_export]
macro_rules! assert_variance {
    ($name:ident) => {
        ::paste::paste! {
            #[cfg(test)]
            fn [<_enlarge_$name:snake>]<'a, 'b>(q: $name<'a>) -> $name<'b> where 'a:'b { q }
        }
    };
}
