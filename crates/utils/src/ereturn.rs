#[macro_export]
/// Early return macro, works with named blocks and regular returns
///
/// # Example
/// ```rust
/// let test = 'a : {
///   break_if!('a, 1 == 2, 1);
///   break_if!('a, true, 2);
///   break_if!('a, true, 3);
///   4
/// };
/// assert_eq(test, 2)
/// ```
macro_rules! ereturn_if {
  ($label:lifetime, $value:expr, $ret:expr) => {
  if $value {
    break $label $ret
  }
  };
  ($value:expr, $ret:expr) => {
  if $value {
    return $ret
  }
  };
  ($label:lifetime, $value:expr) => {
  ereturn_if!($label, $value, ())
  };
  ($value:expr) => {
  ereturn_if!($value, ())
  };
}
