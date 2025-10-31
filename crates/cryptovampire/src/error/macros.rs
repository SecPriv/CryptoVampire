#[macro_export]
macro_rules! error_at {
  ($location:expr, $($t:tt)*) => {
    {
      use $crate::error::LocationProvider;
      $crate::Error::msg_with_location(LocationProvider::provide($location), format!($($t)*))
    }
  };
  (@ $($t:tt)*) =>{
    $crate::error_at!((), $($t)*)
  }
}

/// Simply returns an [Result::Err] with the right location and formatted message
/// If you also want to exit the function [bail_at] might be the better choice
///
/// # Example
/// ```
/// # use cryptovampire::{err_at, error::Location, Result};
/// let err: Result<()> = err_at!(Location::default(), "error message");
/// err.expect_err("");
/// ```
#[macro_export]
macro_rules! err_at  {
    ($location:expr, $($t:tt)*) => {
        Err($crate::error_at!($location, $($t)*))
    };
    (@ $($t:tt)*) => {
      $crate::err_at!((), $($t)*)
    }
}

/// Quit the function with an error a location and formatted message
///
/// # Example
/// ```
/// # use cryptovampire::{bail_at, error::Location};
/// fn test() -> cryptovampire::Result<()> {
///     bail_at!(Location::default(), "error message");
///     unreachable!()
/// }
///
/// test().expect_err("");
/// ```
#[macro_export]
macro_rules! bail_at {
    ($location:expr, $($t:tt)*) => {
        return $crate::err_at!($location, $($t)*)
    };
    (@ $($t:tt)*) => {
      $crate::bail_at!((), $($t)*)
    }
}

/// Copies perfectly `anyhow`'s `bail` macro
///
/// Still here for legacy reasons...
#[macro_export]
macro_rules! bail {
    ($($t:tt)*) => {
        $crate::bail_at!((), $($t)*)
    };
}

/// Simialr to `assert!` but return a [Result]
///
///
/// # Example
/// ```rust
/// # use cryptovampire::ensure;
/// #
/// ensure!((), 1 == 2, "error! {:}", 1).expect_err("");
/// ```
#[macro_export]
macro_rules! ensure {
    ($location:expr, $f:expr, $($t:tt)*) => {
        if $f {
          std::result::Result::Ok(())
        } else {
          use $crate::error::CVContext;
          $crate::error::AssertionError(format!($($t)*)).with_location($location)
        }
    };
}
