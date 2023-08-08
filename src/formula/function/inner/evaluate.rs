use std::collections::HashMap;

use crate::formula::{
    formula::{RichFormula, ARichFormula},
    function::{
        signature::FixedRefSignature,
        traits::{FixedSignature, MaybeEvaluatable},
        Function,
    },
    sort::Sort,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Evaluate<'bump> {
    name: String,
    input_sort: Sort<'bump>,
    ouput_sort: Sort<'bump>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Evaluator<'bump> {
    functions: HashMap<Sort<'bump>, Function<'bump>>,
}

impl<'bump> Evaluator<'bump> {
    pub fn eval(&self, f: impl Into<ARichFormula<'bump>>) -> ARichFormula<'bump> {
        let f  = f.into();
        self.functions.get(&f.get_sort().unwrap()).unwrap().f_a([f])
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Evaluate<'bump> {
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        FixedRefSignature {
            out: self.input_sort,
            args: [self.ouput_sort].into(),
        }
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Evaluate<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        None
    }
}
