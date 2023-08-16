use hashbrown::HashMap;

use crate::{
    formula::{
        formula::ARichFormula,
        function::{
            builtin::{CONDITION_TO_BOOL, MESSAGE_TO_BITSTRING},
            signature::FixedRefSignature,
            traits::{FixedSignature, MaybeEvaluatable},
            Function,
        },
        sort::{
            builtins::{CONDITION, MESSAGE},
            sorted::SortedError,
            Sort,
        },
    },
    utils::traits::NicerError,
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
        let sort = f
            .get_sort()
            .debug_continue_msg(&format!("{f} doesn't have a known sort"))?;
        let fun = self
            .functions
            .get(&sort)
            .ok_or(SortedError::Impossible)
            .debug_continue_msg(&format!("{} isn't in the hashmap", sort.name().as_ref()))?;
        Ok(fun.f_a([f]))
    }

    pub fn functions_mut(&mut self) -> &mut HashMap<Sort<'bump>, Function<'bump>> {
        &mut self.functions
    }

    pub fn functions(&self) -> &HashMap<Sort<'bump>, Function<'bump>> {
        &self.functions
    }
}

impl<'bump> Default for Evaluator<'bump> {
    fn default() -> Self {
        Self {
            functions: [
                (MESSAGE.as_sort(), MESSAGE_TO_BITSTRING.clone()),
                (CONDITION.as_sort(), CONDITION_TO_BOOL.clone()),
            ]
            .into(),
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
