use std::collections::BTreeMap;

use utils::traits::NicerError;

use crate::formula::formula::ARichFormula;
use crate::formula::function::Function;
use crate::formula::function::builtin::{CONDITION_TO_BOOL, MESSAGE_TO_BITSTRING};
use crate::formula::function::signature::FixedRefSignature;
use crate::formula::function::traits::{FixedSignature, MaybeEvaluatable};
use crate::formula::sort::builtins::{CONDITION, MESSAGE};
use crate::formula::sort::sorted::SortedError;
use crate::formula::sort::{FOSort, Sort};
use crate::formula::utils::Applicable;

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
    functions: BTreeMap<FOSort<'bump>, Function<'bump>>,
}

impl<'bump> Evaluator<'bump> {
    pub fn new(functions: BTreeMap<FOSort<'bump>, Function<'bump>>) -> Self {
        Self { functions }
    }

    /// may panic
    ///
    /// use [Self::try_eval()] instead
    pub fn eval(&self, f: impl Into<ARichFormula<'bump>>) -> ARichFormula<'bump> {
        self.try_eval(f).unwrap()
    }

    /// Try to evaluate a term. That is calling the right 'evaluate' function on it
    ///
    /// Return error if it can't decide the sort
    pub fn try_eval(
        &self,
        f: impl Into<ARichFormula<'bump>>,
    ) -> Result<ARichFormula<'bump>, SortedError> {
        let f: ARichFormula<'bump> = f.into();
        // FIXME: can fail because of validity
        // trace!("try eval: {:}", f);
        let sort = f
            .get_sort()
            .debug_continue_msg(|| format!("{f} doesn't have a known sort"))?;
        let fun = self.functions.get(&sort.into());
        match fun {
            None => Ok(f), // unevaluatable sort don't need to be evaluated
            Some(fun) => Ok(fun.f([f])),
        }
    }

    pub fn functions_mut(&mut self) -> &mut BTreeMap<FOSort<'bump>, Function<'bump>> {
        &mut self.functions
    }

    fn functions(&self) -> &BTreeMap<FOSort<'bump>, Function<'bump>> {
        &self.functions
    }

    pub fn get_eval_function(&self, sort: Sort<'bump>) -> Option<Function<'bump>> {
        self.functions.get(&sort.into()).cloned()
    }

    pub fn iter(&self) -> impl Iterator<Item = (Sort<'bump>, Function<'bump>)> + '_ {
        self.functions().iter().map(|(s, f)| (s.as_reference(), *f))
    }

    pub fn iter_functions(&self) -> impl Iterator<Item = Function<'bump>> + '_ {
        self.functions().values().cloned()
    }

    pub fn iter_sorts(&self) -> impl Iterator<Item = Sort<'bump>> + '_ {
        self.functions().keys().map(|s| s.as_reference())
    }
}

impl<'bump> Default for Evaluator<'bump> {
    fn default() -> Self {
        Self {
            functions: [
                (MESSAGE.as_sort().into(), *MESSAGE_TO_BITSTRING),
                (CONDITION.as_sort().into(), *CONDITION_TO_BOOL),
            ]
            .into(),
        }
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Evaluate<'bump> {
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        FixedRefSignature {
            out: self.ouput_sort,
            args: [self.input_sort].into(),
        }
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Evaluate<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        None
    }
}
