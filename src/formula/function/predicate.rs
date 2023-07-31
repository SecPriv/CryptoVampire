
use crate::formula::sort::{Sort, builtins::BOOL};

use super::{traits::{FixedSignature, MaybeEvaluatable}, signature::FixedRefSignature};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Predicate<'bump> {
    pub name: Box<str>,
    pub args: Box<[Sort<'bump>]>,
    // pub out: Sort<'bump>, always bool
}

impl<'bump> Predicate<'bump> {
    pub fn args(&self) -> &[Sort<'bump>] {
        self.args.as_ref()
    }

    pub fn name(&self) -> &str {
        self.name.as_ref()
    }
}

impl<'a, 'bump:'a> FixedSignature<'a, 'bump> for Predicate<'bump> {
    fn as_fixed_signature(&'a self) ->FixedRefSignature<'a, 'bump> {
        FixedRefSignature { out: BOOL.as_sort(), args: self.args.as_ref().into() }
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Predicate<'bump> {
    fn maybe_get_evaluated(&self) -> Option<super::Function<'bump>> {
        None
    }
}