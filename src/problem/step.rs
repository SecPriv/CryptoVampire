use core::fmt::Debug;
use std::{
    cmp::Ordering,
    marker::PhantomData,
    // collections::{HashMap, HashSet},
    ops::Range,
    ptr::NonNull,
    sync::Arc,
};

use itertools::Itertools;

use crate::formula::{
    formula::{meq, RichFormula},
    function::{builtin::LESS_THAN_STEP, Function},
    sort::Sort,
    variable::Variable,
};

// #[derive(Debug)]
// pub struct Protocol {
//     steps: HashMap<String, Step>,
// }

// impl Protocol {
//     pub fn new<I>(steps: I) -> Self
//     where
//         I: Iterator<Item = Step>,
//     {
//         Self {
//             steps: steps.map(|s| (s.name().to_owned(), s)).collect(),
//         }
//     }
// }

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
pub struct Step<'bump> {
    inner: NonNull<InnerStep<'bump>>,
    container: PhantomData<&'bump ()>,
}

// variables from 1 to parameters.len()
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub(crate) struct InnerStep<'bump> {
    name: String,
    /// ie. the parameters of the step
    free_variables: Vec<Variable<'bump>>,
    /// variables that are bound within the step (by a quantifier for instance)
    used_variables: Vec<Variable<'bump>>,
    condition: RichFormula<'bump>,
    message: RichFormula<'bump>,
    function: Function<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MessageOrCondition {
    Message,
    Condition,
}

impl<'bump> Step<'bump> {
    // pub fn new(
    //     name: &str,
    //     variables: Vec<Variable>,
    //     condition: RichFormula,
    //     message: RichFormula,
    //     function: Function,
    // ) -> Self {
    //     let mut used_variables = message.get_used_variables();
    //     used_variables.extend(condition.get_used_variables().into_iter());
    //     debug_assert!(variables.iter().all(|v| used_variables.contains(v)));

    //     let used_variables = used_variables.into_iter().cloned().collect();

    //     Self(Arc::new(InnerStep {
    //         name: name.to_owned(),
    //         free_variables: variables,
    //         used_variables,
    //         condition,
    //         message,
    //         function,
    //     }))
    // }

    // pub fn map<F>(&self, mut f: F) -> Self
    // where
    //     F: FnMut(MessageOrCondition, &RichFormula) -> RichFormula,
    // {
    //     Self(Arc::new(InnerStep {
    //         name: self.0.name.clone(),
    //         free_variables: self.0.free_variables.clone(),
    //         used_variables: self.0.used_variables.clone(),
    //         condition: f(MessageOrCondition::Condition, &self.0.condition),
    //         message: f(MessageOrCondition::Message, &self.0.message),
    //         function: self.0.function.clone(),
    //     }))
    // }

    pub fn name(&self) -> &str {
        &self.as_ref().name
    }

    pub fn parameters<'a>(&'a self) -> impl Iterator<Item = &'a Sort<'bump>>
    where
        'bump: 'a,
    {
        self.free_variables().iter().map(|v| &v.sort)
    }

    pub fn free_variables(&self) -> &Vec<Variable<'bump>> {
        &self.as_ref().free_variables
    }

    pub fn occuring_variables(&self) -> &Vec<Variable<'bump>> {
        &self.as_ref().used_variables
    }

    pub fn vairable_range(&self) -> Range<usize> {
        let min = self
            .occuring_variables()
            .iter()
            .map(|v| v.id)
            .min()
            .unwrap_or(0);
        let max = self
            .occuring_variables()
            .iter()
            .map(|v| v.id)
            .max()
            .unwrap_or(0);
        min..(max + 1)
    }

    pub fn condition(&self) -> &RichFormula<'bump> {
        &self.as_ref().condition
    }

    pub fn message(&self) -> &RichFormula<'bump> {
        &self.as_ref().message
    }

    pub fn function(&self) -> &Function<'bump> {
        &self.as_ref().function
    }

    pub fn apply_condition(&self, args: &[RichFormula<'bump>]) -> RichFormula<'bump> {
        let vars: Vec<_> = (1..=self.arity()).into_iter().collect_vec();
        self.condition().clone().apply_substitution(&vars, args)
    }

    pub fn apply_message(&self, args: &[RichFormula<'bump>]) -> RichFormula<'bump> {
        let vars: Vec<_> = (1..=self.arity()).into_iter().collect_vec();
        self.message().clone().apply_substitution(&vars, args)
    }

    pub fn arity(&self) -> usize {
        self.as_ref().free_variables.len()
    }

    /// strict happen before relation
    pub fn strict_before(a: RichFormula<'bump>, b: RichFormula<'bump>) -> RichFormula<'bump> {
        LESS_THAN_STEP.f([a, b])
    }

    /// happen before or equal
    pub fn before(a: RichFormula<'bump>, b: RichFormula<'bump>) -> RichFormula<'bump> {
        Self::strict_before(a.clone(), b.clone()) | meq(a, b)
    }

    // return `self` as a formula of type `U` using the variables of [free_variables]
    // pub fn as_formula<T, U>(&self, ctx: &T) -> U
    // where
    //     T: FormulaUser<U>,
    // {
    //     ctx.funf(
    //         self.function().clone(),
    //         self.free_variables()
    //             .into_iter()
    //             .cloned()
    //             .map(|v| ctx.varf(v)),
    //     )
    // }
}

impl<'bump> AsRef<InnerStep<'bump>> for Step<'bump> {
    fn as_ref(&self) -> &InnerStep<'bump> {
        unsafe { self.inner.as_ref() } // inner is alive while 'bump is
    }
}

impl<'bump> Debug for Step<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_ref().fmt(f)
    }
}

// impl Clone for Step {
//     fn clone(&self) -> Self {
//         Self(Arc::clone(&self.0))
//     }
// }

// impl PartialEq for Step {
//     fn eq(&self, other: &Self) -> bool {
//         Arc::ptr_eq(&self.0, &other.0)
//     }
// }

// impl Eq for Step {}

impl<'bump> Ord for Step<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            Ordering::Equal
        } else {
            Ord::cmp(self.as_ref(), other.as_ref())
        }
    }
}

impl<'bump> PartialOrd for Step<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(&self, &other))
    }
}
