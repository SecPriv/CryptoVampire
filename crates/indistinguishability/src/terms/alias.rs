use super::{CowExpr, CowPattern};
use crate::terms::Sort;
use serde::Serialize;

/// When the fonction is an alias
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Alias(pub cow![AliasRewrite]);

/// A rewrite rule for an alias
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct AliasRewrite {
    /// These are the arguments to the function that one must unify with to get
    /// rewritten as [Self::to].
    pub from: cow![CowPattern],
    pub to: CowPattern,
    pub variables: cow![egg::Var],
    pub sorts: cow![Sort],
}

impl Alias {
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a AliasRewrite> {
        self.0.iter()
    }
}

#[macro_export]
macro_rules! mk_alias {
    ($( $($var:literal:$sort:ident),* in $($args:expr),* => $to:expr),*) => {
        {
            use $crate::terms::Sort::*;
            $crate::terms::Alias(::std::borrow::Cow::Owned(vec!
            [$($crate::terms::AliasRewrite {
                    from: ::std::borrow::Cow::Owned(vec![$($crate::terms::formula_utils::convert_to_cow($args)),*]),
                    to: $crate::terms::formula_utils::convert_to_cow($to),
                    variables: ::std::borrow::Cow::Owned(vec![$(::egg::Var::from_u32($var)),*]),
                    sorts: ::std::borrow::Cow::Owned(vec![$($sort),*]),
                }
            ),*]
            ))
        }
    };
}
