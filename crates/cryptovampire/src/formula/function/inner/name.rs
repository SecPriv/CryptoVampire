use std::sync::Arc;

use utils::implvec;

use crate::formula::function::Function;
use crate::formula::function::signature::FixedRefSignature;
use crate::formula::function::traits::{FixedSignature, MaybeEvaluatable};
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::NAME;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Name<'bump> {
    name: String,
    target: Sort<'bump>,
    args: Arc<[Sort<'bump>]>,
}

impl<'bump> Name<'bump> {
    pub fn new(name: String, target: Sort<'bump>, args: implvec!(Sort<'bump>)) -> Self {
        Self {
            name,
            target,
            args: args.into_iter().collect(),
        }
    }

    pub fn args(&self) -> &[Sort<'bump>] {
        self.args.as_ref()
    }

    pub fn target(&self) -> Sort<'bump> {
        self.target
    }

    pub fn name(&self) -> &str {
        self.name.as_ref()
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Name<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        None
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Name<'bump> {
    fn as_fixed_signature(
        &'a self,
    ) -> crate::formula::function::signature::FixedRefSignature<'a, 'bump> {
        let args = self.args().into();
        FixedRefSignature { out: *NAME, args }
    }
}
