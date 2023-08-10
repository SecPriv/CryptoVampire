use hashbrown::HashMap;

use crate::formula::{
    formula::ARichFormula,
    function::{
        builtin::MESSAGE_TO_BITSTRING,
        signature::FixedRefSignature,
        traits::{FixedSignature, MaybeEvaluatable},
        Function,
    },
    sort::{builtins::MESSAGE, sorted::SortedError, Sort},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Evaluate<'bump> {
    name: String,
    input_sort: Sort<'bump>,
    ouput_sort: Sort<'bump>,
}

impl<'bump> Evaluate<'bump> {
    pub fn new(name: String, input_sort: Sort<'bump>, ouput_sort: Sort<'bump>) -> Self {
        Self {
            name,
            input_sort,
            ouput_sort,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Evaluator<'bump> {
    functions: HashMap<Sort<'bump>, Function<'bump>>,
}

impl<'bump> Evaluator<'bump> {
    pub fn new(functions: HashMap<Sort<'bump>, Function<'bump>>) -> Self {
        Self { functions }
    }

    /// may panic
    ///
    /// use [Self::try_eval()] instead
    pub fn eval(&self, f: impl Into<ARichFormula<'bump>>) -> ARichFormula<'bump> {
        self.try_eval(f).unwrap()
    }

    pub fn try_eval(
        &self,
        f: impl Into<ARichFormula<'bump>>,
    ) -> Result<ARichFormula<'bump>, SortedError> {
        let f: ARichFormula = f.into();
        Ok(self.functions.get(&f.get_sort()?).unwrap().f_a([f]))
    }

    pub fn functions_mut(&mut self) -> &mut HashMap<Sort<'bump>, Function<'bump>> {
        &mut self.functions
    }
}

impl<'bump> Default for Evaluator<'bump> {
    fn default() -> Self {
        Self {
            functions: [(MESSAGE.as_sort(), MESSAGE_TO_BITSTRING.clone())].into(),
        }
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
