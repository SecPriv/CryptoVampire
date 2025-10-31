use std::sync::Arc;

use utils::string_ref::StrRef;

use super::super::InnerFunction;
use super::super::traits::{MaybeEvaluatable, MaybeFixedSignature};
use crate::formula::function::signature::{Lazy, Signature};
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::BOOL;
use crate::problem::crypto_assumptions::{
    SubtermEufCmaSignKey, SubtermEufCmaSignMain, SubtermIntCtxtKey, SubtermIntCtxtMain,
    SubtermIntCtxtRand, SubtermNonce, SubtermUfCmaKey, SubtermUfCmaMain,
};
use crate::static_signature;
use crate::subterm::kind::{AbsSubtermKindG, SubtermKind, SubtermKindWSort};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Subterm<'bump> {
    subterm: Subsubterm<'bump>,
    name: String,
    target_sort: SubtermKindWSort<'bump>,
}

impl<'bump> Subterm<'bump> {
    pub fn new(
        subterm: Subsubterm<'bump>,
        name: String,
        target_sort: SubtermKindWSort<'bump>,
    ) -> Self {
        Self {
            subterm,
            name,
            target_sort,
        }
    }

    pub fn into_inner_function(self) -> InnerFunction<'bump> {
        InnerFunction::Subterm(self)
    }

    pub fn signature(&self) -> impl Signature<'bump> {
        match self.target_sort {
            AbsSubtermKindG::Regular(s) => {
                Lazy::A(static_signature!((self.subterm.sort(), s) -> BOOL.as_sort()))
            }
            AbsSubtermKindG::Vampire(_) => {
                Lazy::B(signature::SubtermSignature::new(self.subterm.sort()))
            }
        }
    }

    pub fn subterm(&self) -> &Subsubterm<'bump> {
        &self.subterm
    }

    pub fn name(&self) -> StrRef<'_> {
        // self.name.as_ref()
        match self.target_sort {
            AbsSubtermKindG::Vampire(()) => self.name.as_str().into(),
            AbsSubtermKindG::Regular(sort) => format!("{sort}${}", self.name).into(),
        }
    }

    pub fn kind(&self) -> SubtermKind {
        self.subterm.kind()
    }
}

macro_rules! generate {
    ($($name:ident:$t:ty),*) => {
        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
        pub enum Subsubterm<'bump> {
            $($name(Arc<$t>)),*
        }

        impl<'bump> Subsubterm<'bump> {
            pub fn sort(&self) -> Sort<'bump> {
                match self {
                    $(Self::$name(x) => x.sort()),*
                }
            }

            pub fn kind(&self) -> SubtermKind {

                match self {
                    $(Self::$name(x) => x.kind()),*
                }
            }
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
    EufCmaMacMain: SubtermUfCmaMain<'bump>,
    EufCmaMacKey: SubtermUfCmaKey<'bump>,
    EufCmaSignMain: SubtermEufCmaSignMain<'bump>,
    EufCmaSignKey: SubtermEufCmaSignKey<'bump>,
    IntCtxtMain: SubtermIntCtxtMain<'bump>,
    IntCtxtKey: SubtermIntCtxtKey<'bump>,
    IntCtxtRand: SubtermIntCtxtRand<'bump>
);
//  Nonce, EufCmaMacMain, EufCmaMacKey, EufCmaSignMain, EufCmaSignKey, IntCtxtMain, IntCtxtKey, IntCtxtRand

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

mod signature {
    use crate::formula::function::signature::{Impossible, Signature};
    use crate::formula::sort::Sort;
    use crate::formula::sort::builtins::BOOL;
    use crate::formula::sort::sort_proxy::SortProxy;

    #[derive(Debug)]
    pub struct SubtermSignature<'bump> {
        own: Sort<'bump>,
        other: SortProxy<'bump>,
    }

    impl<'bump> SubtermSignature<'bump> {
        pub fn new(own: Sort<'bump>) -> Self {
            Self {
                own,
                other: Default::default(),
            }
        }
    }

    impl<'bump> Signature<'bump> for SubtermSignature<'bump> {
        type Args<'a>
            = [SortProxy<'bump>; 2]
        where
            Self: 'a,
            'bump: 'a;

        type FxSign = Impossible;

        fn out(&self) -> SortProxy<'bump> {
            BOOL.as_sort().into()
        }

        fn args<'a>(&'a self) -> Self::Args<'a>
        where
            'bump: 'a,
        {
            [self.own.into(), self.other.clone()]
        }

        fn fast(self) -> Option<Self::FxSign> {
            None
        }

        fn args_size(&self) -> std::ops::RangeInclusive<utils::infinity::Infinity<usize>> {
            2.into()..=2.into()
        }
    }
}
