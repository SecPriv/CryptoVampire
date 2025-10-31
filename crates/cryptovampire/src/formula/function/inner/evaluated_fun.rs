use utils::string_ref::StrRef;

use super::term_algebra::base_function::BaseFunction;
use crate::formula::function::Function;
use crate::formula::function::signature::FixedRefSignature;
use crate::formula::function::traits::{FixedSignature, MaybeEvaluatable};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct EvaluatedFun<'bump> {
    base: Function<'bump>,
}

impl<'bump> EvaluatedFun<'bump> {
    pub fn new(base: Function<'bump>) -> Self {
        assert_eq!(
            base.as_term_algebra().map(|ta| ta.is_function()),
            Some(true)
        );
        Self { base }
    }

    pub fn base(&self) -> Function<'bump> {
        self.base
    }

    pub fn inner_baase(&self) -> &'bump BaseFunction<'bump> {
        self.base
            .precise_as_term_algebra()
            .and_then(|ta| ta.as_function())
            .unwrap()
    }

    pub fn name(&self) -> StrRef<'_> {
        format!("eval${}", self.base.name()).into()
    }
}

impl<'a, 'bump> FixedSignature<'a, 'bump> for EvaluatedFun<'bump>
where
    'bump: 'a,
{
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        let FixedRefSignature { out, args } = self.inner_baase().as_fixed_signature();
        let out = out.evaluated_sort();
        let args = args.into_iter().map(|s| s.evaluated_sort()).collect();
        // let args = args.unwrap();
        FixedRefSignature { out, args }
    }
}

impl<'bump> MaybeEvaluatable<'bump> for EvaluatedFun<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        None
    }
}
