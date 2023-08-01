use std::sync::Arc;

use crate::problem::{
    crypto_assumptions::{
        SubtermEufCmaMacKey, SubtermEufCmaMacMain, SubtermEufCmaSignKey, SubtermEufCmaSignMain,
        SubtermIntCtxtKey, SubtermIntCtxtMain, SubtermIntCtxtRand, SubtermNonce,
    },
    subterm::kind::SubtermKind,
};

use super::super::{
    traits::{MaybeEvaluatable, MaybeFixedSignature},
    InnerFunction,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Subterm<'bump> {
    pub subterm: Subsubterm<'bump>,
    pub name: String,
}

impl<'bump> Subterm<'bump> {
    pub fn into_inner_function(self) -> InnerFunction<'bump> {
        InnerFunction::Subterm(self)
    }
}

macro_rules! generate {
    ($($name:ident:$t:ty),*) => {
        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
        pub enum Subsubterm<'bump> {
            $($name(Arc<$t>)),*
        }
    };
}

#[macro_export]
macro_rules! do_for_all_subterms {
    ($($name:ident),*;  $val:expr; $v:ident -> $block:block) => {
        match $val {
            $($crate::formula::function::inner::subterm::Subsubterm::$name($v) => {$block}),*
        }
    };
}

generate!(
    Nonce: SubtermNonce<'bump>,
    EufCmaMacMain: SubtermEufCmaMacMain<'bump>,
    EufCmaMacKey: SubtermEufCmaMacKey<'bump>,
    EufCmaSignMain: SubtermEufCmaSignMain<'bump>,
    EufCmaSignKey: SubtermEufCmaSignKey<'bump>,
    IntCtxtMain: SubtermIntCtxtMain<'bump>,
    IntCtxtKey: SubtermIntCtxtKey<'bump>,
    IntCtxtRand: SubtermIntCtxtRand<'bump>
);
//  Nonce, EufCmaMacMain, EufCmaMacKey, EufCmaSignMain, EufCmaSignKey, IntCtxtMain, IntCtxtKey, IntCtxtRand

impl<'bump> Subsubterm<'bump> {
    pub fn kind(&self) -> SubtermKind {
        do_for_all_subterms!(
                Nonce, EufCmaMacMain, EufCmaMacKey, EufCmaSignMain,
                    EufCmaSignKey, IntCtxtMain, IntCtxtKey, IntCtxtRand;
        self; s -> {
            s.kind
        })
    }
}

// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
// pub enum Subsubterm<'bump> {
//     Nonce(Rc<SubtermNonce<'bump>>),
//     EufCmaMacMain(Rc<SubtermEufCmaMacMain<'bump>>),
//     EufCmaMacKey(Rc<SubtermEufCmaMacKey<'bump>>),
//     EufCmaSignMain(Rc<SubtermEufCmaSignMain<'bump>>),
//     EufCmaSignKey(Rc<SubtermEufCmaSignKey<'bump>>),
//     IntCtxtMain(Rc<SubtermIntCtxtMain<'bump>>),
//     IntCtxtKey(Rc<SubtermIntCtxtKey<'bump>>),
//     IntCtxtRand(Rc<SubtermIntCtxtRand<'bump>>),
// }

fn _enlarge<'a, 'b>(q: Subterm<'a>) -> Subterm<'b>
where
    'a: 'b,
{
    q
}

impl<'a, 'bump: 'a> MaybeFixedSignature<'a, 'bump> for Subterm<'bump> {
    fn maybe_fixed_signature(
        &'a self,
    ) -> Option<super::super::signature::FixedRefSignature<'a, 'bump>> {
        None
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Subterm<'bump> {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}
