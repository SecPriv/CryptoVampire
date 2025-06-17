use bon::Builder;
use serde::Serialize;

use crate::{
    LangVar,
    terms::{CowPattern, Sort, formula_utils::convert_to_cow},
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Builder)]
pub struct Rewrite {
    /// These are the arguments to the function that one must unify with to get
    /// rewritten as [Self::to].
    #[builder(with = |x: impl std::iter::IntoIterator<Item = LangVar>| convert_to_cow(x))]
    pub from: CowPattern,
    #[builder(with = |x: impl std::iter::IntoIterator<Item = LangVar>| convert_to_cow(x))]
    pub to: CowPattern,
    #[builder(with = |x: impl std::iter::IntoIterator<Item = egg::Var>| x.into_iter().collect())]
    pub variables: cow![egg::Var],
    #[builder(with = |x: impl std::iter::IntoIterator<Item = Sort>| x.into_iter().collect())]
    pub sorts: cow![Sort],
}

#[macro_export]
macro_rules! mk_rewrite {
    ($($var:literal:$sort:ident),* in $args:expr => $to:expr) => {
        {
          // $crate::terms::Rewrite {
          //         from: $crate::terms::formula_utils::convert_to_cow($args),
          //         to: $crate::terms::formula_utils::convert_to_cow($to),
          //         variables: ::std::borrow::Cow::Owned(vec![$(::egg::Var::from_u32($var)),*]),
          //         sorts: ::std::borrow::Cow::Owned(vec![$($sort),*]),
          //     }
          $crate::terms::Rewrite::builder()
            .from($args)
            .to($to)
            .sorts({ use $crate::terms::Sort::*; [$($sort),*]})
            .variables([$(egg::Var::from_u32($var)),*])
            .build()
        }
    };
}
