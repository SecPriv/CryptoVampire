use core::fmt::Debug;
use std::{ops::Range, sync::Arc};

use itertools::Itertools;

use crate::{
    assert_variance,
    container::{allocator::ContainerTools, contained::Containable, reference::Reference},
    formula::{
        formula::{meq, ARichFormula, RichFormula},
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
        string_ref::StrRef,
        traits::RefNamed,
        utils::{AlreadyInitialized, MaybeInvalid},
    }, smt::smt::{Smt, SmtFormula},
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

pub const INIT_STEP_NAME: &'static str = "init";

pub type Step<'bump> = Reference<'bump, InnerStep<'bump>>;
impl<'bump> Containable<'bump> for InnerStep<'bump> {}
// #[derive(Hash, PartialEq, Eq, Clone, Copy)]
// pub struct Step<'bump> {
//     inner: NonNull<Option<InnerStep<'bump>>>,
//     container: PhantomData<&'bump ()>,
// }

// variables from 1 to parameters.len()
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerStep<'bump> {
    name: String,
    /// ie. the parameters of the step
    free_variables: Arc<[Variable<'bump>]>,
    /// variables that are bound within the step (by a quantifier for instance)
    used_variables: Arc<[Variable<'bump>]>,
    condition: ARichFormula<'bump>,
    message: ARichFormula<'bump>,
    function: Function<'bump>,
}

impl<'bump> InnerStep<'bump> {
    pub fn new(
        name: String,
        free_variables: Arc<[Variable<'bump>]>,
        used_variables: Arc<[Variable<'bump>]>,
        condition: ARichFormula<'bump>,
        message: ARichFormula<'bump>,
        function: Function<'bump>,
    ) -> Self {
        debug_assert!(
            {
                itertools::chain!(message.get_free_vars(), condition.get_free_vars())
                    .all(|v| free_variables.contains(&v))
            },
            "in {name}:\n\tmesg: [{}] in {}\n\tcond: [{}] in {}\n\targs: [{}]",
            message.get_free_vars().iter().join(", "),
            SmtFormula::from_arichformula(message.as_ref()),
            condition.get_free_vars().iter().join(", "),
            SmtFormula::from_arichformula(condition.as_ref()),
            free_variables.iter().join(", ")
        );
        debug_assert!({
            itertools::chain!(message.get_used_variables(), condition.get_used_variables())
                .all(|v| free_variables.contains(&v))
        });

        Self {
            name,
            free_variables,
            used_variables,
            condition,
            message,
            function,
        }
    }
}

assert_variance!(Step);
// asssert_trait!(sync_send_step; InnerStep; Sync, Send);
// unsafe impl<'bump> Sync for Step<'bump> {}
// unsafe impl<'bump> Send for Step<'bump> {}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MessageOrCondition {
    Message,
    Condition,
}

impl<'bump> Step<'bump> {
    pub fn new<C>(
        container: &'bump C,
        name: implderef!(str),
        args: implvec!(Variable<'bump>),
        message: ARichFormula<'bump>,
        condition: ARichFormula<'bump>,
    ) -> Self
    where
        C: ContainerTools<'bump, InnerStep<'bump>, R<'bump> = Self>
            + ContainerTools<'bump, InnerFunction<'bump>, R<'bump> = Function<'bump>>,
    {
        let free_variables: Arc<[_]> = args.into_iter().collect();
        assert!(message
            .get_free_vars()
            .iter()
            .all(|v| free_variables.contains(v)));
        assert!(condition
            .get_free_vars()
            .iter()
            .all(|v| free_variables.contains(v)));

        let used_variables =
            ARichFormula::iter_used_varibales([message.clone(), condition.clone()])
                .unique()
                .collect();

        let (step, _) = container
            .alloc_cyclic(|(step, function)| {
                let inner_step = InnerStep {
                    name: name.to_string(),
                    free_variables,
                    used_variables,
                    condition,
                    message,
                    function: *function,
                };
                let inner_function =
                    InnerFunction::Step(StepFunction::Step(InnerStepFuction::new(*step)));
                (inner_step, inner_function)
            })
            .expect("`step` and `function` should not have been initialized");

        step
    }

    /// **not thread safe**
    ///
    /// returns an error if `step` or `function` was already initialized.
    ///
    /// # Safety
    /// This will mutate `step` and `function` make sure nobody is mutating them
    /// in another thread. Thanks to the check on initialization no one can alias
    /// `step` or `function` other that with an [C::initialize()] function.
    ///
    /// # Panic
    /// This panics `args` does not contain all the free variables in `message` and
    /// `condition`. (Tt can contain more)
    pub unsafe fn new_with_uninit<C>(
        _container: &'bump C,
        name: implderef!(str),
        args: implvec!(Variable<'bump>),
        message: ARichFormula<'bump>,
        condition: ARichFormula<'bump>,

        step: &Step<'bump>,
        function: &Function<'bump>,
    ) -> Result<(), AlreadyInitialized>
    where
        C: ContainerTools<'bump, InnerStep<'bump>, R<'bump> = Self>
            + ContainerTools<'bump, InnerFunction<'bump>, R<'bump> = Function<'bump>>,
    {
        let free_variables: Arc<[_]> = args.into_iter().collect();
        assert!(message
            .get_free_vars()
            .iter()
            .all(|v| free_variables.contains(v)));
        assert!(condition
            .get_free_vars()
            .iter()
            .all(|v| free_variables.contains(v)));
        let used_variables =
            ARichFormula::iter_used_varibales([message.clone(), condition.clone()])
                .unique()
                .collect();
        let inner_step = InnerStep {
            name: name.to_string(),
            free_variables,
            used_variables,
            condition,
            message,
            function: *function,
        };
        let inner_function = InnerFunction::Step(StepFunction::Step(InnerStepFuction::new(*step)));

        C::initialize(step, inner_step)?;
        C::initialize(function, inner_function)?;
        Ok(())
    }

    pub fn name(&self) -> &'bump str {
        self.assert_valid().unwrap();
        &self.precise_as_ref().name
    }

    pub fn parameters(&self) -> impl Iterator<Item = &'bump Sort<'bump>> {
        // self.assert_valid().unwrap();
        self.free_variables().iter().map(|v| &v.sort)
    }

    pub fn free_variables(&self) -> &'bump [Variable<'bump>] {
        self.precise_as_ref().free_variables.as_ref()
    }

    pub fn occuring_variables(&self) -> &'bump [Variable<'bump>] {
        self.precise_as_ref().used_variables.as_ref()
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
        &self.precise_as_ref().condition
    }

    pub fn message(&self) -> &'bump RichFormula<'bump> {
        &self.precise_as_ref().message
    }

    pub fn condition_arc(&self) -> &'bump ARichFormula<'bump> {
        &self.precise_as_ref().condition
    }

    pub fn message_arc(&self) -> &'bump ARichFormula<'bump> {
        &self.precise_as_ref().message
    }

    pub fn function(&self) -> Function<'bump> {
        self.assert_valid().unwrap();
        self.as_inner().function
    }

    pub fn apply_condition(&self, args: &[ARichFormula<'bump>]) -> ARichFormula<'bump> {
        self.assert_valid().unwrap();
        let vars: Vec<_> = (1..=self.arity()).into_iter().collect_vec();
        self.condition().clone().apply_substitution(vars, args)
    }

    pub fn apply_message(&self, args: &[ARichFormula<'bump>]) -> ARichFormula<'bump> {
        self.assert_valid().unwrap();
        let vars: Vec<_> = (1..=self.arity()).into_iter().collect_vec();
        self.message().clone().apply_substitution(vars, args)
    }

    pub fn arity(&self) -> usize {
        self.assert_valid().unwrap();
        self.as_inner().free_variables.len()
    }

    /// strict happen before relation
    pub fn strict_before(a: ARichFormula<'bump>, b: ARichFormula<'bump>) -> ARichFormula<'bump> {
        LESS_THAN_STEP.f_a([a, b])
    }

    /// happen before or equal
    pub fn before(a: ARichFormula<'bump>, b: ARichFormula<'bump>) -> ARichFormula<'bump> {
        Self::strict_before(a.clone(), b.clone()) | meq(a, b)
    }

    /// is it the init step
    pub fn is_init_step(&self) -> bool {
        self.name() == INIT_STEP_NAME
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

    // pub fn maybe_precise_as_ref(&self) -> Result<&'bump InnerStep<'bump>, AccessToInvalidData> {
    //     unsafe { self.inner.as_ref() }
    //         .as_ref()
    //         .ok_or(AccessToInvalidData::Error)
    // }

    // pub fn as_inner(&self) -> &InnerStep<'bump> {
    //     self.precise_as_ref()
    // }
}

impl<'a, 'bump: 'a> RefNamed<'a> for &'a InnerStep<'bump> {
    fn name_ref(&self) -> StrRef<'a> {
        self.name.as_str().into()
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

// impl<'bump> Debug for Step<'bump> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         self.as_inner().fmt(f)
//     }
// }

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

// impl<'bump> Ord for Step<'bump> {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         self.assert_valid().unwrap();
//         if self == other {
//             Ordering::Equal
//         } else {
//             Ord::cmp(self.as_inner(), other.as_inner())
//         }
//     }
// }

// impl<'bump> PartialOrd for Step<'bump> {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         self.assert_valid().unwrap();
//         Some(Ord::cmp(&self, &other))
//     }
// }

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

// impl<'bump> Reference<'bump> for Step<'bump> {
//     type Inner<'a> = InnerStep<'a> where 'a:'bump;

//     fn from_ref(ptr: &'bump Option<InnerStep<'bump>>) -> Self {
//         Self {
//             inner: NonNull::from(ptr),
//             container: Default::default(),
//         }
//     }

//     fn to_ref(&self) -> &'bump Option<Self::Inner<'bump>> {
//         unsafe { self.inner.as_ref() }
//     }
// }

// impl<'bump> AsRef<RefPointee<'bump, Step<'bump>>> for Step<'bump> {
//     fn as_ref(&self) -> &RefPointee<'bump, Step<'bump>> {
//         unsafe { self.inner.as_ref() }
//     }
// }
