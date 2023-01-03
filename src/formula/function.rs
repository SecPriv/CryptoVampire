use std::{
    borrow::Borrow,
    cell::{Ref, RefCell},
    hash::Hash,
    rc::{Rc, Weak},
};

use bitflags::bitflags;

use crate::problem::protocol::Step;

use super::{builtins::types::STEP, env::Environement, sort::Sort};
use core::fmt::Debug;

const BASE_SKOLEM_NAME: &'static str = "m$sk_";
bitflags! {
    #[derive(Default )]
    pub struct FFlags: u32 {
        /// is a step
        const FROM_STEP =           1<<0 | FFlags::TERM_ALGEBRA.bits | FFlags::SPECIAL_EVALUATE.bits;
        /// is a skolem
        const SKOLEM =              1<<1;
        /// is a find such that
        const FIND_SUCH_THAT =      1<<2;
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

        const DESTRUCTOR =          1<<7 | FFlags::TERM_ALGEBRA.bits | FFlags::SPECIAL_EVALUATE.bits;

        const BUILTIN =             1<<8;

        const SUBTERM_FUN =         1<<9;

        const SPLITING =            1<<10;

        const SPECIAL_SUBTERM =     1<<11;

    }
}

// user accessible part

/// A function is just a pointer to some content in memory.
/// Pieces of it are mutable through a RefCell, other are not.
///
/// Most notable, equality is made on pointers to avoid the possibly
/// convoluted content
///
/// Thus one can copy Function around for more or less free and still
/// carry a lot of information arround within them
#[derive(Hash)]
pub struct Function {
    inner: Rc<InnerFunction>,
}

// fast imutable content
#[derive(Debug)]
struct InnerFunction {
    name: String,
    inner: RefCell<InnerInnerFunction>,
}

// slowe mutable content
#[derive(Debug)]
struct InnerInnerFunction {
    input_sorts: Vec<Sort>,
    output_sort: Sort,
    flags: FFlags,

    // more specific
    /// pointer to the evaluate function when it exists.
    ///
    /// I'm using a weak to avoid loops
    evaluate_fun: Option<Weak<InnerFunction>>,
}

impl Ord for InnerInnerFunction {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        todo!()
    }
}

impl PartialOrd for InnerInnerFunction {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl Eq for InnerInnerFunction {}
impl PartialEq for InnerInnerFunction {
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

impl Hash for InnerInnerFunction {
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

impl InnerInnerFunction {
    fn as_tuple(&self) -> (&Vec<Sort>, &Sort, &FFlags) {
        (&self.input_sorts, &self.output_sort, &self.flags)
    }
}

impl Hash for InnerFunction {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl Clone for Function {
    fn clone(&self) -> Self {
        Self {
            inner: Rc::clone(&self.inner),
        }
    }
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for Function {}

impl Ord for Function {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&Rc::as_ptr(&self.inner), &Rc::as_ptr(&other.inner)).then(
            Ord::cmp(self.name(), other.name())
                .then_with(|| self.inner.inner.borrow().cmp(&other.inner.inner.borrow())),
        )
    }
}

impl PartialOrd for Function {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

impl Function {
    pub fn new(name: &str, input_sorts: Vec<Sort>, output_sort: Sort) -> Self {
        Self::hidden_new(name.to_owned(), input_sorts, output_sort, FFlags::empty())
    }

    fn hidden_new(name: String, input_sorts: Vec<Sort>, output_sort: Sort, flags: FFlags) -> Self {
        let innerinner = InnerInnerFunction {
            input_sorts,
            output_sort,
            flags,
            evaluate_fun: None,
        };
        let inner = InnerFunction {
            name: name,
            inner: RefCell::new(innerinner),
        };

        Function {
            inner: Rc::new(inner),
        }
    }
    pub fn new_with_flag(
        name: &str,
        input_sorts: Vec<Sort>,
        output_sort: Sort,
        flags: FFlags,
    ) -> Self {
        Self::hidden_new(name.to_owned(), input_sorts, output_sort, flags)
    }

    pub fn arity(&self) -> usize {
        self.inner.inner.borrow().input_sorts.len()
    }

    pub fn get_input_sorts(&self) -> Ref<'_, Vec<Sort>> {
        Ref::map(self.inner.inner.borrow(), |i| &i.input_sorts)
    }

    pub fn set_input_sorts(&self, v: Vec<Sort>) {
        self.inner.inner.borrow_mut().input_sorts = v
    }

    pub fn get_output_sort(&self) -> Sort {
        self.inner.inner.borrow().output_sort.clone()
    }

    pub fn set_output_sort(&self, v: Sort) {
        self.inner.inner.borrow_mut().output_sort = v
    }

    pub fn name(&self) -> &str {
        &self.inner.name
    }

    fn add_flag(&self, flag: FFlags) {
        // self.0.flags |=flag.bits;
        self.inner.inner.borrow_mut().flags |= flag
    }

    fn remove_flag(&self, flag: FFlags) {
        // self.0.flags.fetch_and((!flag).bits());
        self.inner.inner.borrow_mut().flags.remove(flag)
    }

    fn contain_flag(&self, flag: FFlags) -> bool {
        self.get_flags().contains(flag)
    }

    pub fn is_skolem(&self) -> bool {
        self.contain_flag(FFlags::SKOLEM)
    }

    pub fn is_user_defined(&self) -> bool {
        self.contain_flag(FFlags::USER_DEFINED)
    }

    pub fn is_term_algebra(&self) -> bool {
        self.contain_flag(FFlags::TERM_ALGEBRA)
    }

    pub fn is_special_evaluate(&self) -> bool {
        self.contain_flag(FFlags::SPECIAL_EVALUATE)
    }

    pub fn is_special_subterm(&self) -> bool {
        self.contain_flag(FFlags::SPECIAL_SUBTERM)
    }

    pub fn is_from_step(&self) -> bool {
        self.contain_flag(FFlags::FROM_STEP)
    }

    pub fn contain_sort(&self, s: &Sort) -> bool {
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
    }

    pub fn hard_eq(&self, other: &Self) -> bool {
        (self == other)
            || ((self.name() == other.name())
                && (self.inner.inner.borrow().as_tuple() == other.inner.inner.borrow().as_tuple()))
    }

    pub fn as_ptr_usize(&self) -> usize {
        Rc::as_ptr(&self.inner) as usize
    }
}

impl From<&Step> for Function {
    fn from(s: &Step) -> Self {
        s.function().clone()
    }
}
