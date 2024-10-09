#[macro_export]
macro_rules! bail_at {
    ($location:expr, $($t:tt)*) => {
        return {
          use $crate::error::CVContext;
          use $crate::error::LocationProvider;
          format!($($t)*).with_location(LocationProvider::provide($location))
        }
    };
}