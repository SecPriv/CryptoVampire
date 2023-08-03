use core::fmt::Debug;
use std::{
    cmp::Ordering,
    marker::PhantomData,
    // collections::{HashMap, HashSet},
    ops::Range,
    ptr::NonNull,
};

use itertools::Itertools;

use crate::{
    assert_variance, asssert_trait,
    container::{
        allocator::{Container, ContainerTools},
        reference::{ Reference},
    },
    formula::{
        formula::{meq, RichFormula},
        function::{
            builtin::LESS_THAN_STEP,
            inner::step::{InnerStepFuction, StepFunction},
            Function, InnerFunction,
        },
        sort::Sort,
        variable::Variable,
    },
    implderef, implvec,
    utils::{
        precise_as_ref::PreciseAsRef,
        utils::{AccessToInvalidData, AlreadyInitialized,  MaybeInvalid},
    },
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
    inner: NonNull<Option<InnerStep<'bump>>>,
    container: PhantomData<&'bump ()>,
}

// variables from 1 to parameters.len()
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerStep<'bump> {
    name: String,
    /// ie. the parameters of the step
    free_variables: Vec<Variable<'bump>>,
    /// variables that are bound within the step (by a quantifier for instance)
    used_variables: Vec<Variable<'bump>>,
    condition: RichFormula<'bump>,
    message: RichFormula<'bump>,
    function: Function<'bump>,
}


asssert_trait!(sync_send_step; InnerStep; Sync, Send);
assert_variance!(Step);
unsafe impl<'bump> Sync for Step<'bump> {}
unsafe impl<'bump> Send for Step<'bump> {}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MessageOrCondition {
    Message,
    Condition,
}

impl<'bump> Step<'bump> {
    pub(crate) fn new<C>(
        container: &'bump C,
        name: implderef!(str),
        args: implvec!(Variable<'bump>),
        message: RichFormula<'bump>,
        condition: RichFormula<'bump>,
    ) -> Self
    where
        C: ContainerTools<'bump, (Self, Function<'bump>)>,
    {
        let free_variables = args.into_iter().collect_vec();
        assert!(message
            .get_free_vars()
            .iter()
            .all(|v| free_variables.contains(v)));
        assert!(condition
            .get_free_vars()
            .iter()
            .all(|v| free_variables.contains(v)));

        let used_variables = RichFormula::iter_used_varibales([&message, &condition])
            .unique()
            .collect_vec();

        // let (_, step) = unsafe {
        //     Function::new_cyclic(container, |function| {
        //         let inner_step = InnerStep::Valid {
        //             name: name.to_string(),
        //             free_variables,
        //             used_variables,
        //             condition,
        //             message,
        //             function,
        //         };
        //         let inner_step_ref = container.alloc();
        //         std::ptr::write(inner_step_ref.as_ptr(), inner_step);
        //         let step = Step {
        //             inner: inner_step_ref,
        //             container: Default::default(),
        //         };
        //         (
        //             InnerFunction::Step(StepFunction::Step(InnerStepFuction::new(step))),
        //             step,
        //         )
        //         // all has been allocated
        //     })
        // };

        // let

        // step
        todo!()
    }

    /// new step overwriting `old_function`.
    ///
    /// **Not thread safe**
    pub(crate) unsafe fn new_with_function(
        container: &'bump impl Container<'bump, Step<'bump>>,
        old_function: Function<'bump>,
        name: implderef!(str),
        args: implvec!(Variable<'bump>),
        message: RichFormula<'bump>,
        condition: RichFormula<'bump>,
    ) -> Result<Self, AlreadyInitialized> {
        let free_variables = args.into_iter().collect_vec();
        assert!(message
            .get_free_vars()
            .iter()
            .all(|v| free_variables.contains(v)));
        assert!(condition
            .get_free_vars()
            .iter()
            .all(|v| free_variables.contains(v)));

        // let used_variables = RichFormula::iter_used_varibales([&message, &condition])
        //     .unique()
        //     .collect_vec();
        // let name = name.to_string();
        // let inner = {
        //     let inner_step = InnerStep {
        //         name: name.to_string(),
        //         free_variables,
        //         used_variables,
        //         condition,
        //         message,
        //         function: old_function,
        //     };
        //     let inner_step_ref = container.alloc();
        //     std::ptr::write(inner_step_ref.as_ptr(), inner_step);
        //     inner_step_ref
        // };
        // let step = Step {
        //     inner,
        //     container: Default::default(),
        // };
        // old_function.initiallize(InnerFunction::Step(StepFunction::Step(
        //     InnerStepFuction::new(step),
        // )))?;
        // Ok(step)
        todo!()
    }

    pub fn name(&self) -> &'bump str {
        self.assert_valid().unwrap();
        &self.precise_as_ref().name
    }

    pub fn parameters(&self) -> impl Iterator<Item = &'bump Sort<'bump>> {
        self.assert_valid().unwrap();
        self.free_variables().iter().map(|v| &v.sort)
    }

    pub fn free_variables(&self) -> &'bump Vec<Variable<'bump>> {
        self.assert_valid().unwrap();
        &self.precise_as_ref().free_variables
    }

    pub fn occuring_variables(&self) -> &'bump Vec<Variable<'bump>> {
        self.assert_valid().unwrap();
        &self.precise_as_ref().used_variables
    }

    pub fn vairable_range(&self) -> Range<usize> {
        self.assert_valid().unwrap();
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

    pub fn condition(&self) -> &'bump RichFormula<'bump> {
        self.assert_valid().unwrap();
        &self.precise_as_ref().condition
    }

    pub fn message(&self) -> &'bump RichFormula<'bump> {
        self.assert_valid().unwrap();
        &self.precise_as_ref().message
    }

    pub fn function(&self) -> Function<'bump> {
        self.assert_valid().unwrap();
        self.as_inner().function
    }

    pub fn apply_condition(&self, args: &[RichFormula<'bump>]) -> RichFormula<'bump> {
        self.assert_valid().unwrap();
        let vars: Vec<_> = (1..=self.arity()).into_iter().collect_vec();
        self.condition().clone().apply_substitution(vars, args)
    }

    pub fn apply_message(&self, args: &[RichFormula<'bump>]) -> RichFormula<'bump> {
        self.assert_valid().unwrap();
        let vars: Vec<_> = (1..=self.arity()).into_iter().collect_vec();
        self.message().clone().apply_substitution(vars, args)
    }

    pub fn arity(&self) -> usize {
        self.assert_valid().unwrap();
        self.as_inner().free_variables.len()
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

    pub fn maybe_precise_as_ref(&self) -> Result<&'bump InnerStep<'bump>, AccessToInvalidData> {
        unsafe { self.inner.as_ref() }
            .as_ref()
            .ok_or(AccessToInvalidData::Error)
    }

    pub fn as_inner(&self) -> &InnerStep<'bump> {
        self.precise_as_ref()
    }
}

// impl<'bump> PreciseAsRef<'bump, IInnerStep<'bump>> for Step<'bump> {
//     fn precise_as_ref(&self) -> &'bump IInnerStep<'bump> {
//         self.maybe_precise_as_ref().unwrap()
//     }
// }

// impl<'bump> AsRef<IInnerStep<'bump>> for Step<'bump> {
//     fn as_ref(&self) -> &IInnerStep<'bump> {
//         // the validity check is made before
//         self.precise_as_ref()
//     }
// }

impl<'bump> Debug for Step<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_inner().fmt(f)
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
        self.assert_valid().unwrap();
        if self == other {
            Ordering::Equal
        } else {
            Ord::cmp(self.as_inner(), other.as_inner())
        }
    }
}

impl<'bump> PartialOrd for Step<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.assert_valid().unwrap();
        Some(Ord::cmp(&self, &other))
    }
}

// impl<'bump> FromNN<'bump> for Step<'bump> {
//     type Inner = InnerStep<'bump>;

//     unsafe fn from_nn(inner: NonNull<Self::Inner>) -> Self {
//         Self {
//             inner,
//             container: Default::default(),
//         }
//     }
// }

// impl<'bump> LateInitializable for Step<'bump> {
//     type Inner = IInnerStep<'bump>;

//     unsafe fn inner_overwrite(&self, other: Self::Inner) {
//         std::ptr::drop_in_place(self.inner.as_ptr());
//         std::ptr::write(self.inner.as_ptr(), Some(other));
//     }
// }

// impl<'bump> MaybeInvalid for Step<'bump> {
//     fn is_valid(&self) -> bool {
//         self.maybe_precise_as_ref().is_ok()
//     }
// }

impl<'bump> Reference<'bump> for Step<'bump> {
    type Inner<'a> = InnerStep<'a> where 'a:'bump;

    fn from_ref(ptr: &'bump Option<InnerStep<'bump>>) -> Self {
        Self {
            inner: NonNull::from(ptr),
            container: Default::default(),
        }
    }

    fn to_ref(&self) -> &'bump Option<Self::Inner<'bump>> {
        unsafe { self.inner.as_ref() }
    }
}

// impl<'bump> AsRef<RefPointee<'bump, Step<'bump>>> for Step<'bump> {
//     fn as_ref(&self) -> &RefPointee<'bump, Step<'bump>> {
//         unsafe { self.inner.as_ref() }
//     }
// }
