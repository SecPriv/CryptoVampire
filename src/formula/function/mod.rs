// pub mod base_function;
pub mod booleans;
pub mod builtin;
pub mod evaluate;
pub mod function_like;
pub mod if_then_else;
pub mod nonce;
pub mod predicate;
pub mod step;
pub mod subterm;
pub mod term_algebra;
pub mod unused;

// pub mod equality;
use std::{cmp::Ordering, hash::Hash, marker::PhantomData, ptr::NonNull};

use bitflags::bitflags;

// use crate::problem::step::Step;

use crate::{
    container::{self, Container, NameFinder, ScopeAllocator},
    utils::precise_as_ref::PreciseAsRef,
};

use self::{
    booleans::Booleans, evaluate::Evaluate, if_then_else::IfThenElse, nonce::Nonce,
    predicate::Predicate, step::StepFunction, subterm::Subterm, term_algebra::TermAlgebra, unused::Unused,
};

use super::{
    formula::RichFormula,
    sort::{
        sorted::{Sorted, SortedError},
        Sort,
    },
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
    Unused(Unused<'bump>)
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
    // inner: Rc<IIFunction>,
    // pub inner: &'bump InnerFunction<'bump>,
    inner: NonNull<InnerFunction<'bump>>,
    container: PhantomData<&'bump ()>,
}

unsafe impl<'bump> Sync for Function<'bump> {}
unsafe impl<'bump> Send for Function<'bump> {}

impl<'bump> Sorted<'bump> for Function<'bump> {
    fn sort(&self, _args: &[Sort<'bump>]) -> Result<Sort<'bump>, SortedError> {
        todo!()
    }
}

/* // fast imutable content
#[derive(Debug)]
struct IIFunction {
    name: String,
    inner: RefCell<IIIFunction>,
}

// slowe mutable content
#[derive(Debug)]
struct IIIFunction {
    input_sorts: Vec<Sort>,
    output_sort: Sort,
    flags: FFlags,

    // more specific
    /// pointer to the evaluate function when it exists.
    ///
    /// I'm using a weak to avoid loops
    evaluate_fun: Option<Weak<IIFunction>>,
}

impl Ord for IIIFunction {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(
            &(&self.input_sorts, &self.output_sort, &self.flags),
            &(&other.input_sorts, &other.output_sort, &other.flags),
        )
    }
}

impl PartialOrd for IIIFunction {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl Eq for IIIFunction {}
impl PartialEq for IIIFunction {
    fn eq(&self, other: &Self) -> bool {
        self.input_sorts == other.input_sorts
            && self.output_sort == other.output_sort
            && self.flags == other.flags
            && match (
                self.evaluate_fun.as_ref().map(|f| f.upgrade()),
                other.evaluate_fun.as_ref().map(|f| f.upgrade()),
            ) {
                (Some(Some(a)), Some(Some(b))) => Rc::ptr_eq(&a, &b),
                _ => false,
            }
    }
}

impl Hash for IIIFunction {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.input_sorts.hash(state);
        self.output_sort.hash(state);
        self.flags.hash(state);
        self.evaluate_fun
            .as_ref()
            .map(|f| f.upgrade().hash(state))
            .hash(state);
    }
}

impl IIIFunction {
    fn as_tuple(&self) -> (&Vec<Sort>, &Sort, &FFlags) {
        (&self.input_sorts, &self.output_sort, &self.flags)
    }
}

impl Hash for IIFunction {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
} */

impl<'b> Debug for Function<'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

/* impl Clone for Function {
    fn clone(&self) -> Self {
        Self {
            inner: Rc::clone(&self.inner),
        }
    }
} */

// impl<'bump> PartialEq for Function<'bump> {
//     fn eq(&self, other: &Self) -> bool {
//         Rc::ptr_eq(&self.inner, &other.inner)
//     }
// }

// impl<'bump> Eq for Function<'bump> {}

impl<'bump> Ord for Function<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Ord::cmp(&Rc::as_ptr(&self.inner), &Rc::as_ptr(&other.inner)).then(
        //     Ord::cmp(self.name(), other.name())
        //         .then_with(|| self.inner.inner.borrow().cmp(&other.inner.inner.borrow())),
        // )
        if self == other {
            Ordering::Equal
        } else {
            // Ord::cmp(self.name(), other.name())
            // .then(Ord::cmp(
            //     &(Rc::as_ptr(&self.inner) as usize),
            //     &(Rc::as_ptr(&other.inner) as usize),
            // ))
            // .then_with(|| self.inner.inner.borrow().cmp(&other.inner.inner.borrow()))
            Ord::cmp(self.as_ref(), other.as_ref())
        }
    }
}

impl<'bump> PartialOrd for Function<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

impl<'bump> Function<'bump> {
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
        let name = container.find_free_name("split");
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

    // pub fn new(name: &str, input_sorts: Vec<Sort>, output_sort: Sort) -> Self {
    //     Self::hidden_new(name.to_owned(), input_sorts, output_sort, FFlags::empty())
    // }

    // fn hidden_new(name: String, input_sorts: Vec<Sort>, output_sort: Sort, flags: FFlags) -> Self {
    //     let innerinner = IIIFunction {
    //         input_sorts,
    //         output_sort,
    //         flags,
    //         evaluate_fun: None,
    //     };
    //     let inner = IIFunction {
    //         name: name,
    //         inner: RefCell::new(innerinner),
    //     };

    //     Function {
    //         inner: Rc::new(inner),
    //     }
    // }
    // pub fn new_with_flag(
    //     name: &str,
    //     input_sorts: Vec<Sort>,
    //     output_sort: Sort,
    //     flags: FFlags,
    // ) -> Self {
    //     Self::hidden_new(name.to_owned(), input_sorts, output_sort, flags)
    // }

    pub fn fast_outsort(&self) -> Option<Sort<'bump>> {
        todo!()
    }
    pub fn forced_input_sort(&self) -> &[Sort<'bump>] {
        todo!()
    }

    /*     pub fn arity(&self) -> usize {
        self.inner.inner.borrow().input_sorts.len()
    }

    pub fn get_input_sorts(&self) -> Ref<'_, Vec<Sort>> {
        Ref::map(self.inner.inner.borrow(), |i| &i.input_sorts)
    }

    pub fn set_input_sorts(&self, v: Vec<Sort>) {
        self.inner.inner.borrow_mut().input_sorts = v
    }

    pub fn set_sort_fun<F>(&self, f: F)
    where
        F: Fn(Sort) -> Sort,
    {
        let mut inner = self.inner.inner.borrow_mut();
        take_mut::take(&mut inner.output_sort, |s| f(s));
        for s in inner.input_sorts.iter_mut() {
            take_mut::take(s, |s| f(s))
        }
    }

    pub fn get_output_sort(&self) -> Sort {
        self.inner.inner.borrow().output_sort.clone()
    }

    pub fn set_output_sort(&self, v: Sort) {
        self.inner.inner.borrow_mut().output_sort = v
    } */

    pub fn name(&self) -> &str {
        // &self.inner.name
        todo!()
    }

    // #[allow(dead_code)]
    // fn add_flag(&self, flag: FFlags) {
    //     // self.0.flags |=flag.bits;
    //     self.inner.inner.borrow_mut().flags |= flag
    // }

    // #[allow(dead_code)]
    // fn remove_flag(&self, flag: FFlags) {
    //     // self.0.flags.fetch_and((!flag).bits());
    //     self.inner.inner.borrow_mut().flags.remove(flag)
    // }

    // fn contain_flag(&self, flag: FFlags) -> bool {
    //     self.get_flags().contains(flag)
    // }

    // pub fn is_skolem(&self) -> bool {
    //     self.contain_flag(FFlags::SKOLEM)
    // }

    // pub fn is_user_defined(&self) -> bool {
    //     self.contain_flag(FFlags::USER_DEFINED)
    // }

    // pub fn is_term_algebra(&self) -> bool {
    //     self.contain_flag(FFlags::TERM_ALGEBRA)
    // }

    // pub fn is_special_evaluate(&self) -> bool {
    //     self.contain_flag(FFlags::SPECIAL_EVALUATE)
    // }

    // pub fn is_special_subterm(&self) -> bool {
    //     self.contain_flag(FFlags::SPECIAL_SUBTERM)
    // }

    // pub fn is_from_step(&self) -> bool {
    //     self.contain_flag(FFlags::FROM_STEP)
    // }

    // pub fn is_from_quantifer(&self) -> bool {
    //     self.contain_flag(FFlags::FROM_QUANTIFIER)
    // }

    // pub fn is_cell(&self) -> bool {
    //     self.contain_flag(FFlags::CELL)
    // }

    /*     pub fn contain_sort(&self, s: &Sort) -> bool {
        self.sort_iter().any(|fs| fs.eq(s))
    }

    pub fn get_flags(&self) -> FFlags {
        self.inner.inner.borrow().flags
    }

    pub fn sort_iter(&'_ self) -> impl Iterator<Item = Ref<'_, Sort>> {
        std::iter::successors(
            Some((
                0,
                Ref::map(self.inner.inner.borrow(), |inn| &inn.output_sort),
            )),
            |(i, _)| {
                let inner = self.inner.inner.borrow();
                if *i < inner.input_sorts.len() {
                    Some((i + 1, Ref::map(inner, |inn| &inn.input_sorts[*i])))
                } else {
                    None
                }
            },
        )
        .map(|(_, s)| s)
    }

    pub fn input_sorts_iter(&'_ self) -> impl Iterator<Item = Ref<'_, Sort>> {
        self.sort_iter().skip(1)
    }

    pub fn generate_new_destructor(&self) -> Vec<Function> {
        debug_assert!(
            self.is_term_algebra(),
            "'{}' isn't in the term algebra, a destructor wouldn't make sense",
            self.name()
        );

        self.get_input_sorts()
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let name = format!("d${}_{}", self.name(), i);
                Function::new_with_flag(
                    &name,
                    vec![self.get_output_sort().clone()],
                    s.clone(),
                    FFlags::DESTRUCTOR,
                )
            })
            .collect()
    }

    pub fn is_built_in(&self) -> bool {
        self.contain_flag(FFlags::BUILTIN)
    }

    pub fn new_step(env: &Environement, name: &str, sorts: &Vec<Sort>) -> Self {
        Self::new_with_flag(name, sorts.clone(), STEP(env).clone(), Self::step_flags())
    }

    pub fn step_flags() -> FFlags {
        FFlags::FROM_STEP | FFlags::TERM_ALGEBRA
    }

    pub fn get_evaluate_name(&self) -> Option<String> {
        self.get_evaluate_function().map(|f| f.name().to_owned())
    }

    pub fn get_evaluate_function(&self) -> Option<Function> {
        self.inner
            .inner
            .borrow()
            .evaluate_fun
            .as_ref()
            .map(|f| f.upgrade().map(|inner| Function { inner }))
            .flatten()
    }

    pub fn set_evaluate_functions(&self, f: &Function) {
        self.inner.inner.borrow_mut().evaluate_fun = Some(Rc::downgrade(&f.inner))
    } */

    // pub fn hard_eq(&self, other: &Self) -> bool {
    //     (self == other)
    //         || ((self.name() == other.name())
    //             && (self.inner.inner.borrow().as_tuple() == other.inner.inner.borrow().as_tuple()))
    // }

    // pub fn as_ptr_usize(&self) -> usize {
    //     // Rc::as_ptr(self.inner) as usize
    //     self.inner.as_ptr() as usize
    // }

    // pub fn f<T, U>(self, ctx: &T, args: impl IntoIterator<Item = U>) -> U
    // where
    //     T: FormulaUser<U>,
    // {
    //     ctx.funf(self, args)
    // }

    pub fn f<'bbump>(
        &self,
        args: impl IntoIterator<Item = RichFormula<'bbump>>,
    ) -> RichFormula<'bbump>
    where
        'bump: 'bbump,
    {
        assert!(!matches!(self.inner(), InnerFunction::Unused(_)));

        RichFormula::Fun(*self, args.into_iter().collect())
    }

    // pub fn cf<T, U>(&self, ctx: &T, args: impl IntoIterator<Item = U>) -> U
    // where
    //     T: FormulaUser<U>,
    // {
    //     self.clone().f(ctx, args)
    // }

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

fn enlarge<'a, 'b>(q: Function<'a>) -> Function<'b>
where
    'a: 'b,
{
    q
}
