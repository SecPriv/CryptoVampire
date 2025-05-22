use crate::SmtFormula;

#[macro_export]
macro_rules! smt_formulas {
  ((forall ($((#$var:ident!$i:literal $s:expr))* ) $($t:tt)*)) => {
      {
          $(let $var = $crate::SmtFormula::Var($i);)*
          $crate::SmtFormula::Forall(
                  vec![
                      $($crate::SortedVar {var:$i, sort:$s}),*
                  ],
                  Box::new($crate::smt_formulas!($($t)*))
          )
      }
  };
  ((exists ($(($var:ident!i:literal $s:expr))* ) $($t:tt)*)) => {
      {
          $(let $var = $crate::SmtFormula::Var($i);)*
          $crate::SmtFormula::Exists(
                  vec![
                      $($crate::SortedVar {var:$i, sort:$s}),*
                  ],
                  Box::new($crate::smt_formulas!($($t)*)
          )
      }
  };


  (#$l:literal) => {
      $l.into()
  };
  (#$l:ident) => {
      $l.into()
  };
  (#($l:expr)) => {
      $l.into()
  };

  (true) => {
    $crate::SmtFormula::True
  };
  (false) => {
    $crate::SmtFormula::False
  };
  ((and $($args:tt)*)) => {
    $crate::SmtFormula::And(vec![$($crate::smt_formulas!($args)),*])
  };
  ((or $($args:tt)*)) => {
    $crate::SmtFormula::Or(vec![$($crate::smt_formulas!($args)),*])
  };
  ((= $($args:tt)*)) => {
    $crate::SmtFormula::Eq(vec![$($crate::smt_formulas!($args)),*])
  };
  ((distinct $($args:tt)*)) => {
    $crate::SmtFormula::Neq(vec![$($crate::smt_formulas!($args)),*])
  };
  ((not $arg:tt)) => {
    $crate::SmtFormula::Not($crate::smt_formulas!($arg))
  };

  ($l:ident) => {
      $crate::SmtFormula::Fun($l, vec![])
  };

  (($l:ident $($args:tt)*)) => {
      $crate::SmtFormula::Fun($l, vec![$($crate::smt_formulas!($args)),*])
  }
}

#[test]
fn test() {
    let tmp = "a";
    let t: SmtFormula<&'static str, &'static str> = smt_formulas! {
        (forall ((#a!1 "s")) (tmp #a #a))
    };
}
