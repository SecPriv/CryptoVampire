use std::collections::HashMap;

use crate::formula::{
    formula::RichFormula,
    function::{
        signature::FixedRefSignature,
        traits::{FixedSignature, MaybeEvaluatable},
        Function,
    },
    sort::{builtins::NAME, Sort},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Name<'bump> {
    name: String,
    target: Sort<'bump>,
    args: Vec<Sort<'bump>>,
}

impl<'bump> Name<'bump> {
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NameCaster<'bump> {
    content: HashMap<Sort<'bump>, Function<'bump>>,
}

impl<'bump> NameCaster<'bump> {
    pub fn cast_function(&self, sort: &Sort<'bump>) -> Option<&Function<'bump>> {
        self.content.get(&sort)
    }

    pub fn cast(&self, sort: Sort<'bump>, f: RichFormula<'bump>) -> RichFormula<'bump> {
        self.cast_function(&sort).unwrap().f([f])
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
        let args =  self.args().into();
        FixedRefSignature {
            out: NAME.clone(),
            args,
        }
    }
}
