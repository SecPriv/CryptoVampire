#[macro_export]
macro_rules! error_at {
  ($location:expr, $($t:tt)*) => {
    {
      use $crate::error::LocationProvider;
      crate::Error::msg_with_location(LocationProvider::provide($location), format!($($t)*))
    }
  };
  (@ $($t:tt)*) =>{
    $crate::error_at!((), $($t)*)
  }
}

#[macro_export]
macro_rules! err_at  {
    ($location:expr, $($t:tt)*) => {
        Err($crate::error_at!($location, $($t)*))
    };
    (@ $($t:tt)*) => {
      $crate::err_at!((), $($t)*)
    }
}

#[macro_export]
macro_rules! bail_at {
    ($location:expr, $($t:tt)*) => {
        return $crate::err_at!($location, $($t)*)
    };
    (@ $($t:tt)*) => {
      $crate::bail_at!((), $($t)*)
    }
}

#[macro_export]
macro_rules! bail {
    ($($t:tt)*) => {
        $crate::bail_at!((), $($t)*)
    };
}

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
