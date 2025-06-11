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
macro_rules! ebreak_let {
  ($label:lifetime, let $pat:pat = $value:expr, $ret:expr) => {
    let $pat = $value else {
      break $label $ret
    }
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
macro_rules! econtinue_let {
  ($label:lifetime, let $pat:pat = $value:expr) => {
    let $pat = $value else {
      continue $label
    }
  };
  (let $pat:pat = $value:expr) => {
    let $pat = $value else {
      continue
    };
  };
}
