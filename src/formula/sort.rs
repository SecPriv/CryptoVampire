use bitflags::bitflags;
use core::fmt::Debug;
use std::{fmt::Display, rc::Rc, cmp::Ordering};

bitflags! {
    #[derive(Default )]
    pub struct SFlags: u32 {
        const TERM_ALGEBRA =        1<<0;
        const BUILTIN_VAMPIRE =     1<<1;
        const EVALUATABLE =         1<<2;
    }
}

#[derive(Hash)]
pub enum Sort {
    BuiltIn(&'static InnerSort),
    Dynamic(Rc<InnerSort>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct InnerSort {
    name: String,
    flags: SFlags,
}

impl Debug for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl PartialEq for Sort {
    fn eq(&self, other: &Self) -> bool {
        // Arc::ptr_eq(&self.0, &other.0)
        // self.0.name == other.0.name
        std::ptr::eq(self.as_ref(), other.as_ref())
    }
}

impl Eq for Sort {}

impl Ord for Sort {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Ord::cmp(&Rc::as_ptr(&self.0), &Rc::as_ptr(&other.0))
        if self != other {
            Ord::cmp(
                &self.as_ptr_usize(),
                &self.as_ptr_usize(),
            )
        } else {
            Ordering::Equal
        }
    }
}

impl PartialOrd for Sort {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

impl Clone for Sort {
    fn clone(&self) -> Self {
        // Self(Rc::clone(&self.0))
        match self {
            Sort::BuiltIn(s) => Sort::BuiltIn(s),
            Sort::Dynamic(s) => Sort::Dynamic(Rc::clone(s)),
        }
    }
}

impl<'a> From<&'a str> for Sort {
    fn from(str: &'a str) -> Self {
        Self::new(str)
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_ref().name)
    }
}

impl Sort {
    pub fn new(str: &str) -> Self {
        Sort::Dynamic(Rc::new(InnerSort {
            name: str.to_owned(),
            flags: SFlags::empty(),
        }))
    }
    pub fn new_with_flag(str: &str, flags: SFlags) -> Self {
        Sort::Dynamic(Rc::new(InnerSort {
            name: str.to_owned(),
            flags,
        }))
    }

    pub fn name(&self) -> &str {
        &self.as_ref().name
    }

    pub fn is_term_algebra(&self) -> bool {
        self.as_ref().flags.contains(SFlags::TERM_ALGEBRA)
    }

    pub fn is_built_in(&self) -> bool {
        self.as_ref().flags.contains(SFlags::BUILTIN_VAMPIRE)
    }

    pub fn is_evaluatable(&self) -> bool {
        self.as_ref().flags.contains(SFlags::EVALUATABLE)
    }

    pub fn as_ptr_usize(&self) -> usize {
        self.as_ref() as *const InnerSort as usize
    }
}

impl AsRef<InnerSort> for Sort {
    fn as_ref(&self) -> &InnerSort {
        match self {
            Sort::BuiltIn(s) => s,
            Sort::Dynamic(s) => s.as_ref(),
        }
    }
}
