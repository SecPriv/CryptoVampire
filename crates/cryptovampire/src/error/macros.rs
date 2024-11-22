#[macro_export]
macro_rules! error_at {
  ($location:expr, $($t:tt)*) => {
    {
      use $crate::error::LocationProvider;
      crate::Error::msg_with_location(LocationProvider::provide($location), format!($($t)*))
    }
  }
}

#[macro_export]
macro_rules! err_at  {
    ($location:expr, $($t:tt)*) => {
        Err($crate::error_at!($location, $($t)*))
    };
}

#[macro_export]
macro_rules! bail_at {
    ($location:expr, $($t:tt)*) => {
        return $crate::err_at!($location, $($t)*)
    };
}