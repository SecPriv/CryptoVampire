use std::ops::Deref;

use utils::string_ref::StrRef;
use utils::vecref::{VecRef, VecRefClone};

use crate::formula::function::Function;
use crate::formula::function::signature::FixedRefSignature;
use crate::formula::function::traits::{FixedSignature, MaybeEvaluatable};
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::NAME;

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
