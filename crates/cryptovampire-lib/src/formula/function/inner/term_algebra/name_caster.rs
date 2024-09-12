use std::ops::Deref;

use crate::formula::{
    function::{
        signature::FixedRefSignature,
        traits::{FixedSignature, MaybeEvaluatable},
        Function,
    },
    sort::{builtins::NAME, Sort},
};
use utils::{
    string_ref::StrRef,
    vecref::{VecRef, VecRefClone},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct NameCaster<'bump> {
    target: Sort<'bump>,
}

impl<'bump> NameCaster<'bump> {
    pub fn new(target: Sort<'bump>) -> Self {
        Self { target }
    }

    pub fn target(&self) -> Sort<'bump> {
        self.target
    }

    pub fn name(&self) -> StrRef<'_> {
        format!("cast${}$name", self.target.name()).into()
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for NameCaster<'bump> {
    fn as_fixed_signature(
        &'a self,
    ) -> crate::formula::function::signature::FixedRefSignature<'a, 'bump> {
        FixedRefSignature {
            out: self.target(),
            args: VecRefClone::VecRef(VecRef::Single(Deref::deref(&NAME))),
        }
    }
}

impl<'bump> MaybeEvaluatable<'bump> for NameCaster<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        None
    }
}
