use crate::{formula::sort::Sort, utils::string_ref::StrRef};

use super::super::{
    signature::FixedRefSignature,
    traits::{MaybeEvaluatable, MaybeFixedSignature},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InvalidFunction<'bump> {
    pub name: Option<StrRef<'bump>>,
    pub args: Option<Vec<Sort<'bump>>>,
    pub sort: Option<Sort<'bump>>,
}

impl<'bump> InvalidFunction<'bump> {
    pub fn name(&self) -> Option<&str> {
        self.name.as_ref().map(AsRef::as_ref)
    }

    pub fn args(&self) -> Option<&[Sort<'bump>]> {
        self.args.as_ref().map(Vec::as_slice)
    }

    pub fn sort(&self) -> Option<Sort<'bump>> {
        self.sort
    }
}

impl<'a, 'bump: 'a> MaybeFixedSignature<'a, 'bump> for InvalidFunction<'bump> {
    fn maybe_fixed_signature(&'a self) -> Option<FixedRefSignature<'a, 'bump>> {
        let out = self.sort()?;
        let args = self.args()?.into();

        Some(FixedRefSignature { out, args })
    }
}

impl<'bump> MaybeEvaluatable<'bump> for InvalidFunction<'bump> {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}
