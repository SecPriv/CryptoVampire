use super::super::signature::FixedRefSignature;
use super::super::traits::{FixedSignature, MaybeEvaluatable};
use crate::formula::sort::Sort;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Skolem<'bump> {
    pub name: Box<str>,
    pub args: Box<[Sort<'bump>]>,
    pub sort: Sort<'bump>,
}

impl<'bump> Skolem<'bump> {
    pub fn sort(&self) -> &Sort<'bump> {
        &self.sort
    }

    pub fn args(&self) -> &[Sort<'bump>] {
        self.args.as_ref()
    }

    pub fn name(&self) -> &str {
        self.name.as_ref()
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Skolem<'bump> {
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        FixedRefSignature {
            out: self.sort,
            args: self.args().into(),
        }
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Skolem<'bump> {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}
