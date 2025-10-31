use crate::formula::function::signature::Signature;
use crate::formula::function::traits::{MaybeEvaluatable, MaybeFixedSignature};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct IfThenElse;

impl IfThenElse {
    pub fn signature<'bump>() -> impl Signature<'bump> {
        signature::ITESignature::default()
    }

    pub fn name() -> &'static str {
        "ite"
    }
}

impl<'a, 'bump: 'a> MaybeFixedSignature<'a, 'bump> for IfThenElse {
    fn maybe_fixed_signature(
        &'a self,
    ) -> Option<super::super::signature::FixedRefSignature<'a, 'bump>> {
        None
    }
}

impl<'bump> MaybeEvaluatable<'bump> for IfThenElse {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}

mod signature {
    use crate::formula::function::signature::{Impossible, Signature};
    use crate::formula::sort::builtins::BOOL;
    use crate::formula::sort::sort_proxy::SortProxy;

    #[derive(Debug, Default)]
    pub struct ITESignature<'bump> {
        sort: SortProxy<'bump>,
    }

    impl<'bump> Signature<'bump> for ITESignature<'bump> {
        type Args<'a>
            = [SortProxy<'bump>; 3]
        where
            Self: 'a,
            'bump: 'a;

        type FxSign = Impossible;

        fn out(&self) -> SortProxy<'bump> {
            self.sort.clone()
        }

        fn args<'a>(&'a self) -> Self::Args<'a>
        where
            'bump: 'a,
        {
            [BOOL.as_sort().into(), self.sort.clone(), self.sort.clone()]
        }

        fn fast(self) -> Option<Self::FxSign> {
            None
        }

        fn args_size(&self) -> std::ops::RangeInclusive<utils::infinity::Infinity<usize>> {
            3.into()..=3.into()
        }
    }
}
