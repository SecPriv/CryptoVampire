use std::{hash::Hash, sync::Arc};

use bitflags::bitflags;
use crossbeam_utils::atomic::AtomicCell;

use super::sort::Sort;
use core::fmt::Debug;

const BASE_SKOLEM_NAME: &'static str = "m$sk_";
bitflags! {
    #[derive(Default )]
    pub struct Flags: u32 {
        /// is a step
        const FROM_STEP =           1<<0;
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

    }
}

#[derive(Hash)]
pub struct Function(Arc<InnerFunction>);

#[derive(Debug)]
struct InnerFunction {
    name: String,
    input_sorts: Vec<Sort>,
    output_sort: Sort,
    flags: AtomicCell<u32>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct InnerFunctionFrozen<'a> {
    name: &'a String,
    input_sorts: &'a Vec<Sort>,
    output_sort: &'a Sort,
    flags: u32,
}

impl<'a> From<&'a InnerFunction> for InnerFunctionFrozen<'a> {
    fn from(f: &'a InnerFunction) -> Self {
        InnerFunctionFrozen {
            name: &f.name,
            input_sorts: &f.input_sorts,
            output_sort: &f.output_sort,
            flags: f.flags.load(),
        }
    }
}

impl InnerFunction {
    fn freeze<'a>(&'a self) -> InnerFunctionFrozen<'a> {
        self.into()
    }
}

impl Hash for InnerFunction {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.freeze().hash(state);
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Clone for Function {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Function {}

impl Ord for Function {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&Arc::as_ptr(&self.0), &Arc::as_ptr(&other.0))
    }
}

impl PartialOrd for Function {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.0.freeze().cmp(&other.0.freeze()))
    }
}

impl Function {
    pub fn new(name: &str, input_sorts: Vec<Sort>, output_sort: Sort) -> Self {
        Function(Arc::new(InnerFunction {
            name: name.to_owned(),
            input_sorts,
            output_sort,
            flags: AtomicCell::new(Flags::empty().bits()),
        }))
    }
    pub fn new_with_flag(
        name: &str,
        input_sorts: Vec<Sort>,
        output_sort: Sort,
        flag: Flags,
    ) -> Self {
        Function(Arc::new(InnerFunction {
            name: name.to_owned(),
            input_sorts,
            output_sort,
            flags: AtomicCell::new(flag.bits()),
        }))
    }

    pub fn set_user_defined(&self) {
        self.add_flag(Flags::USER_DEFINED)
    }

    pub fn set_from_step(&self) {
        self.add_flag(Flags::FROM_STEP)
    }

    pub fn set_skolem(&self) {
        self.add_flag(Flags::SKOLEM)
    }

    pub fn arity(&self) -> usize {
        self.0.input_sorts.len()
    }

    pub fn get_input_sorts(&self) -> &[Sort] {
        self.0.as_ref().input_sorts.as_slice()
    }

    pub fn get_output_sort(&self) -> &Sort {
        &self.0.output_sort
    }

    pub fn name(&self) -> &str {
        &self.0.name
    }

    fn add_flag(&self, flag: Flags) {
        self.0.flags.fetch_or(flag.bits);
    }

    fn remove_flag(&self, flag: Flags) {
        self.0.flags.fetch_and((!flag).bits());
    }

    fn contain_flag(&self, flag: Flags) -> bool {
        unsafe {
            // all operations are done through Flag
            Flags::from_bits_unchecked(self.0.flags.load())
        }
        .contains(flag)
    }

    pub fn is_skolem(&self) -> bool {
        self.contain_flag(Flags::SKOLEM)
    }

    pub fn is_user_defined(&self) -> bool {
        self.contain_flag(Flags::USER_DEFINED)
    }

    pub fn is_term_algebra(&self) -> bool {
        self.contain_flag(Flags::TERM_ALGEBRA)
    }

    pub fn is_special_evaluate(&self) -> bool {
        self.contain_flag(Flags::SPECIAL_EVALUATE)
    }

    pub fn contain_sort(&self, s: &Sort) -> bool {
        self.get_input_sorts().contains(s) || self.get_output_sort() == s
    }

    pub fn get_flags(&self) -> Flags {
        unsafe {
            // all operations are done through Flag
            Flags::from_bits_unchecked(self.0.flags.load())
        }
    }
}
