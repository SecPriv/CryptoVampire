// pub mod base_function;
pub mod booleans;
pub mod builtin;
pub mod evaluate;
pub mod function_like;
pub mod if_then_else;
pub mod invalid_function;
pub mod nonce;
pub mod predicate;
pub mod skolem;
pub mod step;
pub mod subterm;
pub mod term_algebra;
pub mod unused;

// pub mod equality;
use std::{cmp::Ordering, hash::Hash, marker::PhantomData, ops::Deref, ptr::NonNull};

use bitflags::bitflags;
use itertools::Itertools;

// use crate::problem::step::Step;

use crate::{
    assert_variance, asssert_trait,
    container::{FromNN, NameFinder, ScopeAllocator},
    formula::function::term_algebra::base_function::{BaseFunction, InnerBaseFunction},
    implderef, implvec,
    problem::cell::MemoryCell,
    utils::{
        precise_as_ref::PreciseAsRef,
        string_ref::StrRef,
        utils::{MaybeInvalid, Reference},
    },
};

use self::{
    booleans::Booleans,
    evaluate::Evaluate,
    if_then_else::IfThenElse,
    invalid_function::InvalidFunction,
    nonce::Nonce,
    predicate::Predicate,
    skolem::Skolem,
    step::StepFunction,
    subterm::Subterm,
    term_algebra::{
        base_function::BaseFunctionTuple,
        cell::Cell,
        quantifier::{get_next_quantifer_id, InnerQuantifier, Quantifier},
        TermAlgebra,
    },
    unused::Tmp,
};

use super::{
    formula::{self, RichFormula},
    quantifier,
    sort::{
        sorted::{Sorted, SortedError},
        Sort,
    },
    variable::Variable,
};
use core::fmt::Debug;

// const BASE_SKOLEM_NAME: &'static str = "m$sk_";
bitflags! {
    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
    pub struct FFlags: u32 {
        /// is a step
        const FROM_STEP =           1<<0 | FFlags::TERM_ALGEBRA.bits() | FFlags::SPECIAL_EVALUATE.bits();
        /// is a skolem
        const SKOLEM =              1<<1;
        /// is a find such that
        // const FIND_SUCH_THAT =      1<<2;
        const FROM_QUANTIFIER =     1<<2;
        /// introduced by the user
        const USER_DEFINED =        1<<3;
        /// will be defined as part as the term algebra in smt
        /// and will have its sorts turned into the ta sorts
        const TERM_ALGEBRA =        1<<4;
        /// is the evaluate equivalent of a [`Flags::TERM_ALGEBRA`]
        const EVALUATE_TA =         1<<5;
        /// automations will skip this function when generating the
        /// translation for ta to evaluate
        const SPECIAL_EVALUATE =    1<<6;

        const DESTRUCTOR =          1<<7 | FFlags::TERM_ALGEBRA.bits() | FFlags::SPECIAL_EVALUATE.bits();

        const BUILTIN =             1<<8;

        const SUBTERM_FUN =         1<<9;

        const SPLITING =            1<<10;

        const SPECIAL_SUBTERM =     1<<11;

        const CELL =                1<<12 | FFlags::SPECIAL_EVALUATE.bits() | FFlags::SPECIAL_SUBTERM.bits() | FFlags::TERM_ALGEBRA.bits();

    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum InnerFunction<'bump> {
    Bool(Booleans),
    Nonce(Nonce<'bump>),
    Step(StepFunction<'bump>),
    Subterm(Subterm<'bump>),
    TermAlgebra(TermAlgebra<'bump>),
    IfThenElse(IfThenElse),
    Evaluate(Evaluate<'bump>),
    Predicate(Predicate<'bump>),
    Tmp(Tmp<'bump>),
    Skolem(Skolem<'bump>),
    Invalid(InvalidFunction<'bump>),
}

// pub struct InnerFunction

// user accessible part

/// A function is just a pointer to some content in memory.
/// Pieces of it are mutable through a RefCell, other are not.
///
/// Most notable, equality is made on pointers to avoid the possibly
/// convoluted content
///
/// Thus one can copy Function around for more or less free and still
/// carry a lot of information arround within them
#[derive(Hash, Clone, Copy, PartialEq, Eq)]
pub struct Function<'bump> {
    inner: NonNull<InnerFunction<'bump>>,
    container: PhantomData<&'bump ()>,
}

asssert_trait!(sync_and_send; InnerFunction; Sync, Send);
assert_variance!(Function);
assert_variance!(InnerFunction);

unsafe impl<'bump> Sync for Function<'bump> {}
unsafe impl<'bump> Send for Function<'bump> {}

impl<'bump> Sorted<'bump> for Function<'bump> {
    fn sort(&self, _args: &[Sort<'bump>]) -> Result<Sort<'bump>, SortedError> {
        todo!()
    }
}

impl<'b> Debug for Function<'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'bump> Ord for Function<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            Ordering::Equal
        } else {
            Ord::cmp(self.as_ref(), other.as_ref())
        }
    }
}

impl<'bump> PartialOrd for Function<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

impl<'bump> Reference for Function<'bump> {
    type Inner = InnerFunction<'bump>;

    unsafe fn overwrite(&self, other: Self::Inner) {
        std::ptr::drop_in_place(self.inner.as_ptr());
        std::ptr::write(self.inner.as_ptr(), other);
    }
}

impl<'bump> Function<'bump> {
    pub fn new_from_inner(
        container: &'bump impl ScopeAllocator<'bump, InnerFunction<'bump>>,
        inner: InnerFunction<'bump>,
    ) -> Self {
        unsafe {
            let ptr = container.alloc();
            std::ptr::write(ptr.as_ptr(), inner);
            Function {
                inner: ptr,
                container: Default::default(),
            }
        }
    }

    /// *safety*: do not call `f`, it is not initialised yet
    pub unsafe fn new_cyclic<F, T>(
        container: &'bump impl ScopeAllocator<'bump, InnerFunction<'bump>>,
        f: F,
    ) -> (Self, T)
    where
        F: FnOnce(Function<'bump>) -> (InnerFunction<'bump>, T),
        T: Sized,
    {
        let ptr = container.alloc();
        let fun = Function {
            inner: ptr,
            container: Default::default(),
        };
        let (inner, t) = f(fun);
        std::ptr::write(fun.inner.as_ptr(), inner);
        (fun, t)
    }

    pub fn new_spliting(
        container: &'bump (impl ScopeAllocator<'bump, InnerFunction<'bump>>
                    + NameFinder<Function<'bump>>),
        sorts: impl IntoIterator<Item = Sort<'bump>>,
    ) -> Self {
        Self::new_predicate(container, sorts, "split")
    }

    pub fn new_rewrite_function(
        container: &'bump (impl ScopeAllocator<'bump, InnerFunction<'bump>>
                    + NameFinder<Function<'bump>>),
        sort: Sort<'bump>,
    ) -> Self {
        Self::new_predicate(container, [sort, sort], &format!("rewrite_{}", sort.name()))
    }

    fn new_predicate(
        container: &'bump (impl ScopeAllocator<'bump, InnerFunction<'bump>>
                    + NameFinder<Function<'bump>>),
        sorts: impl IntoIterator<Item = Sort<'bump>>,
        name: &str,
    ) -> Self {
        let name = container.find_free_name(name);
        let inner = InnerFunction::Predicate(Predicate {
            name: name.into(),
            args: sorts.into_iter().collect(),
        });

        let inner = unsafe {
            let ptr = container.alloc();
            std::ptr::write(ptr.as_ptr(), inner);
            ptr
        };
        Function {
            inner,
            container: Default::default(),
        }
    }

    pub fn new_unused_destructors(
        container: &'bump (impl ScopeAllocator<'bump, InnerFunction<'bump>>
                    + NameFinder<Function<'bump>>),
        constructor: Self,
    ) -> Vec<Self> {
        assert!(constructor.is_term_algebra());

        let o_sort = constructor.fast_outsort().unwrap();
        constructor
            .forced_input_sort()
            .iter()
            .enumerate()
            .map(|(i, &s)| {
                let name = container.find_free_name(&format!("dest_{}_{}", constructor.name(), i));
                Self::new_tmp(container, name, [o_sort], s)
            })
            .collect()
    }

    pub fn new_tmp(
        container: &'bump impl ScopeAllocator<'bump, InnerFunction<'bump>>,
        name: implderef!(str),
        input_sorts: implvec!(Sort<'bump>),
        output_sort: Sort<'bump>,
    ) -> Self {
        let inner = InnerFunction::Tmp(Tmp {
            name: name.to_string(),
            in_sorts: input_sorts.into_iter().collect(),
            out_sort: output_sort,
        });

        let inner = unsafe {
            let ptr = container.alloc();
            std::ptr::write(ptr.as_ptr(), inner);
            ptr
        };
        Function {
            inner,
            container: Default::default(),
        }
    }

    pub fn new_skolem(
        container: &'bump (impl ScopeAllocator<'bump, InnerFunction<'bump>>
                    + NameFinder<Function<'bump>>),
        free_sorts: impl IntoIterator<Item = Sort<'bump>>,
        out: Sort<'bump>,
    ) -> Self {
        {
            let name = container.find_free_name("sk_");
            let inner = InnerFunction::Skolem(Skolem {
                name: name.into(),
                in_sort: free_sorts.into_iter().collect(),
                out_sort: out,
            });

            let inner = unsafe {
                let ptr = container.alloc();
                std::ptr::write(ptr.as_ptr(), inner);
                ptr
            };
            Function {
                inner,
                container: Default::default(),
            }
        }
    }

    pub fn new_quantifier_from_quantifier(
        container: &'bump (impl ScopeAllocator<'bump, InnerFunction<'bump>>
                    + NameFinder<Function<'bump>>),
        q: quantifier::Quantifier<'bump>,
        arg: Box<RichFormula<'bump>>,
    ) -> Self {
        let id = get_next_quantifer_id();
        // let name = container.find_free_name(&format!("c_{}_{}", q.name(), id));

        let free_variables = arg
            .get_free_vars()
            .into_iter()
            .filter(|v| q.get_variables().contains(v))
            .cloned()
            .collect();

        let inner = match &q {
            quantifier::Quantifier::Exists { .. } => InnerQuantifier::Exists { content: arg },
            quantifier::Quantifier::Forall { .. } => InnerQuantifier::Forall { content: arg },
        };

        let bound_variables = match q {
            quantifier::Quantifier::Exists { variables, .. }
            | quantifier::Quantifier::Forall { variables, .. } => variables.into(),
        };

        let inner = InnerFunction::TermAlgebra(TermAlgebra::Quantifier(Quantifier {
            bound_variables,
            free_variables,
            id,
            inner,
        }));
        let inner = unsafe {
            let ptr = container.alloc();
            std::ptr::write(ptr.as_ptr(), inner);
            ptr
        };
        Function {
            inner,
            container: Default::default(),
        }
    }

    /// returns the function and the array of free variables
    pub fn new_find_such_that(
        container: &'bump (impl ScopeAllocator<'bump, InnerFunction<'bump>>
                    + NameFinder<Function<'bump>>),
        vars: implvec!(Variable<'bump>),
        condition: RichFormula<'bump>,
        success: RichFormula<'bump>,
        failure: RichFormula<'bump>,
    ) -> (Self, Vec<Variable<'bump>>) {
        let id = get_next_quantifer_id();

        let vars: Box<[_]> = vars.into_iter().collect();

        let free_variables = [&condition, &success, &failure]
            .into_iter()
            .flat_map(|f| f.get_free_vars().into_iter().cloned())
            .filter(|v| !vars.contains(v))
            .unique()
            .collect_vec();

        if cfg!(debug_assertions) {
            for (v1, v2) in itertools::Itertools::cartesian_product(
                free_variables.iter(),
                free_variables.iter(),
            ) {
                assert!(
                    (v1.id != v2.id) || (v1.sort == v2.sort),
                    "\n\tv1: {:?}\n\tv2: {:?}",
                    v1,
                    v2
                )
            }
        }

        let inner = InnerFunction::TermAlgebra(TermAlgebra::Quantifier(
            term_algebra::quantifier::Quantifier {
                id,
                bound_variables: vars,
                free_variables: free_variables.iter().cloned().collect(),
                inner: term_algebra::quantifier::InnerQuantifier::FindSuchThat {
                    condition: Box::new(condition),
                    success: Box::new(success),
                    faillure: Box::new(failure),
                },
            },
        ));
        (Self::new_from_inner(container, inner), free_variables)
    }

    pub fn new_uninit(
        container: &'bump impl ScopeAllocator<'bump, InnerFunction<'bump>>,
        name: Option<implderef!(str)>,
        input_sorts: Option<implvec!(Sort<'bump>)>,
        output_sort: Option<Sort<'bump>>,
    ) -> Self {
        Self::new_from_inner(
            container,
            InnerFunction::Invalid(InvalidFunction {
                name: name.map(|n| n.to_owned().into()),
                args: input_sorts.map(|i| i.into_iter().collect()),
                sort: output_sort,
            }),
        )
    }

    pub fn new_user_term_algebra(
        container: &'bump impl ScopeAllocator<'bump, InnerFunction<'bump>>,
        name: implderef!(str),
        input_sorts: implvec!(Sort<'bump>),
        output_sort: Sort<'bump>,
    ) -> BaseFunctionTuple<'bump> {
        assert!(output_sort.is_term_algebra());
        let (eval, main) = unsafe {
            Self::new_cyclic(container, |eval_fun| {
                let main_fun = Self::new_from_inner(
                    container,
                    InnerFunction::TermAlgebra(TermAlgebra::Function(BaseFunction::Base(
                        InnerBaseFunction {
                            name: name.to_string().into(),
                            args: input_sorts.into_iter().collect(),
                            out: output_sort,
                            eval_fun,
                        },
                    ))),
                );
                let ref_to_main_inner = match main_fun.precise_as_ref() {
                    InnerFunction::TermAlgebra(TermAlgebra::Function(bfun)) => bfun,
                    _ => unreachable!(),
                };

                let eval_inner = InnerFunction::TermAlgebra(TermAlgebra::Function(
                    BaseFunction::Eval(ref_to_main_inner),
                ));

                (eval_inner, main_fun)
            })
        };
        BaseFunctionTuple { main, eval }
    }

    pub fn fast_outsort(&self) -> Option<Sort<'bump>> {
        todo!()
    }
    pub fn forced_input_sort(&self) -> &[Sort<'bump>] {
        todo!()
    }

    pub fn name(&self) -> StrRef<'bump> {
        // &self.inner.name
        todo!()
    }

    pub fn get_cell(&self) -> Option<MemoryCell<'bump>> {
        match self.as_ref() {
            InnerFunction::TermAlgebra(TermAlgebra::Cell(c)) => Some(c.memory_cell()),
            _ => None,
        }
    }

    pub fn f<'bbump>(
        &self,
        args: impl IntoIterator<Item = RichFormula<'bbump>>,
    ) -> RichFormula<'bbump>
    where
        'bump: 'bbump,
    {
        assert!(!matches!(self.inner(), InnerFunction::Tmp(_)));

        RichFormula::Fun(*self, args.into_iter().collect())
    }

    pub fn inner(&self) -> &InnerFunction<'bump> {
        self.as_ref()
    }

    pub fn is_term_algebra(&self) -> bool {
        match self.as_ref() {
            InnerFunction::TermAlgebra(_) => true,
            _ => false,
        }
    }

    pub fn is_default_subterm(&self) -> bool {
        match self.as_ref() {
            InnerFunction::TermAlgebra(f) => f.is_default_subterm(),
            _ => false,
        }
    }

    /// does this function hide something (ie. quantifier, memory cell, input,...)
    pub fn need_extraction(&self) -> bool {
        match self.as_ref() {
            InnerFunction::TermAlgebra(TermAlgebra::Cell(_))
            | InnerFunction::TermAlgebra(TermAlgebra::Quantifier(_))
            | InnerFunction::TermAlgebra(TermAlgebra::Input) => true,
            _ => false,
        }
    }

    pub(crate) fn from_ptr_inner(inner: NonNull<InnerFunction<'bump>>) -> Self {
        Function {
            inner,
            container: Default::default(),
        }
    }
}

impl<'bump> PreciseAsRef<'bump, InnerFunction<'bump>> for Function<'bump> {
    fn precise_as_ref(&self) -> &'bump InnerFunction<'bump> {
        unsafe { self.inner.as_ref() } // container is alive
    }
}

impl<'bump> AsRef<InnerFunction<'bump>> for Function<'bump> {
    fn as_ref(&self) -> &InnerFunction<'bump> {
        self.precise_as_ref()
    }
}

// impl From<&Step> for Function {
//     fn from(s: &Step) -> Self {
//         s.function().clone()
//     }
// }

pub fn new_static_function(inner: InnerFunction<'static>) -> Function<'static> {
    let inner = NonNull::new(Box::into_raw(Box::new(inner))).unwrap();
    Function {
        inner,
        container: Default::default(),
    }
}

impl<'bump> FromNN<'bump> for Function<'bump> {
    type Inner = InnerFunction<'bump>;

    unsafe fn from_nn(inner: NonNull<Self::Inner>) -> Self {
        Function {
            inner,
            container: Default::default(),
        }
    }
}

impl<'bump> MaybeInvalid for InnerFunction<'bump> {
    fn valid(&self) -> bool {
        todo!()
    }
}

impl<'bump> MaybeInvalid for Function<'bump> {
    fn valid(&self) -> bool {
        let Function { inner, .. } = self;
        (!inner.as_ptr().is_null()) && self.as_ref().valid()
    }
}
