use std::collections::HashMap;

use crate::formula::{formula::RichFormula, sort::Sort};

use super::{signature::FixedRefSignature, traits::FixedSignature, Function};

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
    pub fn eval(&self, f: RichFormula<'bump>) -> RichFormula<'bump> {
        self.functions.get(&f.get_sort().unwrap()).unwrap().f([f])
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
