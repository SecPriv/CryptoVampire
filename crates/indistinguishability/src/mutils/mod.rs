// pub mod linked_list;
// mod bag;
// pub use bag::Bag;

use std::borrow::Cow;

use egg::{Language, SearchMatches};

pub fn to_owned_search_result<'a, 'b, L: Language + Clone>(
    SearchMatches {
        eclass,
        substs,
        ast,
    }: SearchMatches<'a, L>,
) -> SearchMatches<'b, L> {
    SearchMatches {
        eclass,
        substs,
        ast: ast.map(|ast| Cow::Owned(ast.into_owned())),
    }
}

mod subterm;
pub use subterm::*;

mod recexpr;
pub use recexpr::*;

mod term_helpers {
    use egg::{Analysis, EGraph, Id};

    use crate::formula::grammar::TA;

    pub fn is_nonce<N:Analysis<TA>>(egraph: &EGraph<TA, N>, id: Id) -> bool {
        egraph[id].iter().any(|l| l.is_equiv())
    }
}