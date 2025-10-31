#[macro_export]
/// Early return macro that works with named blocks and regular returns.
///
/// This macro provides a way to conditionally return from a function or block,
/// similar to how `if` expressions work, but for early returns.
///
/// # Examples
///
/// ## Basic usage with return values:
/// ```rust
/// fn test() -> i32 {
///     ereturn_if!(true, 42);
///     0
/// }
/// assert_eq!(test(), 42);
/// ```
///
/// ## Usage in named blocks:
/// ```rust
/// let test = 'a : {
///   ereturn_if!('a, 1 == 2, 1);
///   ereturn_if!('a, true, 2);
///   ereturn_if!('a, true, 3);
///   4
/// };
/// assert_eq!(test, 2)
/// ```
///
/// ## Usage without return value:
/// ```rust
/// fn test() {
///     ereturn_if!(true); // returns immediately
///     panic!("This line is unreachable");
/// }
/// ```
macro_rules! ereturn_if {
    ($value:expr, $ret:expr) => {
        if $value {
            return $ret;
        }
    };
    ($value:expr) => {
        ereturn_if!($value, ())
    };
}

#[macro_export]
/// Early break macro that works with named blocks and regular breaks.
///
/// This macro provides a way to conditionally break from a loop or block,
/// similar to how `if` expressions work, but for early breaks.
///
/// # Examples
///
/// ## Basic usage:
/// ```rust
/// 'a: {
///     ebreak_if!(true, 42);
///     panic!("This line is unreachable");
/// }
/// ```
///
/// ## Usage in named blocks:
/// ```rust
/// let test = 'a : {
///   ebreak_if!('a, 1 == 2, 1);
///   ebreak_if!('a, true, 2);
///   ebreak_if!('a, true, 3);
///   4
/// };
/// assert_eq!(test, 2)
/// ```
///
/// ## Usage without return value:
/// ```rust
/// 'a: {
///     ebreak_if!(true); // breaks immediately
///     panic!("This line is unreachable");
/// }
/// ```
macro_rules! ebreak_if {
  ($label:lifetime, $value:expr, $ret:expr) => {
    if $value {
      break $label $ret
    }
  };
  ($label:lifetime, $value:expr) => {
    ebreak_if!($label, $value, ());
  };

  ($value:expr, $ret:expr) => {
    if $value {
      break $ret
    }
  };
  ($value:expr) => {
    ebreak_if!($value, ())
  };
}

#[macro_export]
/// Early continue macro that works with named blocks and regular continues.
///
/// This macro provides a way to conditionally continue a loop,
/// similar to how `if` expressions work, but for early continues.
///
/// # Examples
///
/// ## Basic usage:
/// ```rust
/// let mut i = 0;
/// 'a: loop {
///     econtinue_if!(i < 5);
///     break;
/// }
/// ```
///
/// ## Usage in named blocks:
/// ```rust
/// let mut i = 0;
/// 'a: loop {
///   econtinue_if!('a, i < 5);
///   break;
/// }
/// ```
macro_rules! econtinue_if {
  ($label:lifetime, $value:expr) => {
    if $value {
      continue $label
    }
  };

  ($value:expr) => {
    if $value {
      continue
    }
  };
}

#[macro_export]
/// Early return macro with pattern matching.
///
/// This macro provides a way to conditionally return from a function or block,
/// using pattern matching. If the pattern fails, it returns immediately.
///
/// # Examples
///
/// ## Basic usage:
/// ```rust
/// fn test() -> i32 {
///     ereturn_let!(let Some(x) = Some(42), x);
///     0
/// }
/// assert_eq!(test(), 42);
/// ```
///
/// ## Usage without return value:
/// ```rust
/// fn test() {
///     ereturn_let!(let Some(_) = None); // returns immediately
///     panic!("This line is unreachable");
/// }
/// ```
macro_rules! ereturn_let {
  (let $pat:pat = $value:expr, $ret:expr) => {
    let $pat = $value else {
      return $ret
    };
  };
  (let $pat:pat = $value:expr) => {
    ereturn_let!(let $pat = $value, ())
  };
}

#[macro_export]
macro_rules! ereturn_cf {
    ($e:expr) => {
        match $e {
            ::core::ops::ControlFlow::Continue(x) => x,
            ::core::ops::ControlFlow::Break(x) => return x,
        }
    };
}

#[macro_export]
macro_rules! ebreak_cf {
    ($e:expr) => {
        match $e {
          ::core::ops::ControlFlow::Continue(x) => x,
          ::core::ops::ControlFlow::Break(x) => break x,
        }
    };
    ($lt:lifetime, $e:expr) => {
        match $e {
          ::core::ops::ControlFlow::Continue(x) => x,
          ::core::ops::ControlFlow::Break(x) => break $lt x,
        }
    };
}

#[macro_export]
macro_rules! continue_cf {
    ($e:expr) => {
        match $e {
          ::core::ops::control_flow::ControlFlow::Continue(x) => x,
          ::core::ops::control_flow::ControlFlow::Break(x) => continue x,
        }
    };
    ($lt:lifetime, $e:expr) => {
        match $e {
          ::core::ops::control_flow::ControlFlow::Continue(x) => x,
          ::core::ops::control_flow::ControlFlow::Break(x) => continue $lt x,
        }
    };
}

#[macro_export]
/// Early break macro with pattern matching.
///
/// This macro provides a way to conditionally break from a loop or block,
/// using pattern matching. If the pattern fails, it breaks immediately.
///
/// # Examples
///
/// ## Basic usage:
/// ```rust
/// let test = 'a : {
///   ebreak_let!('a, let Some(x) = None, x);
///   42
/// };
/// assert_eq!(test, 42)
/// ```
///
/// ## Usage in named blocks:
/// ```rust
/// let test = 'a : {
///   ebreak_let!('a, let Some(x) = Some(1), x);
///   42
/// };
/// assert_eq!(test, 1)
/// ```
///
/// ## Usage without return value:
/// ```rust
/// let test = 'a : {
///   ebreak_let!('a, let Some(_) = None);
///   42
/// };
/// assert_eq!(test, 42)
/// ```
macro_rules! ebreak_let {
  ($label:lifetime, let $pat:pat = $value:expr, $ret:expr) => {
    let $pat = $value else {
      break $label $ret
    };
  };
  ($label:lifetime, let $pat:pat = $value:expr) => {
    ebreak_let!($label, let $pat = $value, ())
  };
  (let $pat:pat = $value:expr, $ret:expr) => {
    let $pat = $value else {
      break $ret
    };
  };
  (let $pat:pat = $value:expr) => {
    ebreak_let!(let $pat = $value, ())
  };
}

#[macro_export]
/// Early continue macro with pattern matching.
///
/// This macro provides a way to conditionally continue a loop,
/// using pattern matching. If the pattern fails, it continues immediately.
///
/// # Examples
///
/// ## Basic usage:
/// ```rust
/// let mut i = 0;
/// 'a: loop {
///   econtinue_let!('a, let Some(_) = None);
///   i += 1;
///   if i >= 5 { break; }
/// }
/// ```
macro_rules! econtinue_let {
  ($label:lifetime, let $pat:pat = $value:expr) => {
    let $pat = $value else {
      continue $label
    };
  };
  (let $pat:pat = $value:expr) => {
    let $pat = $value else {
      continue
    };
  };
}
