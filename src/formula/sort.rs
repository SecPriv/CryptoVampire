use bitflags::bitflags;
use core::fmt::Debug;
use std::{fmt::Display, rc::Rc};

bitflags! {
    #[derive(Default )]
    pub struct SFlags: u32 {
        const TERM_ALGEBRA =        1<<0;
        const BUILTIN_VAMPIRE =     1<<1;
        const EVALUATABLE =         1<<2;
    }
}

#[derive(Hash)]
pub struct Sort(Rc<InnerSort>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct InnerSort {
    name: String,
    flags: SFlags,
}

impl Debug for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl PartialEq for Sort {
    fn eq(&self, other: &Self) -> bool {
        // Arc::ptr_eq(&self.0, &other.0)
        self.0.name == other.0.name
    }
}

impl Eq for Sort {}

impl Ord for Sort {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&Rc::as_ptr(&self.0), &Rc::as_ptr(&other.0))
    }
}

impl PartialOrd for Sort {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl Clone for Sort {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<'a> From<&'a str> for Sort {
    fn from(str: &'a str) -> Self {
        Self::new(str)
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.name)
    }
}

impl Sort {
    pub fn new(str: &str) -> Self {
        Sort(Rc::new(InnerSort {
            name: str.to_owned(),
            flags: SFlags::empty(),
        }))
    }
    pub fn new_with_flag(str: &str, flags: SFlags) -> Self {
        Sort(Rc::new(InnerSort {
            name: str.to_owned(),
            flags,
        }))
    }

    pub fn name(&self) -> &str {
        &&self.0.name
    }

    pub fn is_term_algebra(&self) -> bool {
        self.0.flags.contains(SFlags::TERM_ALGEBRA)
    }

    pub fn is_built_in(&self) -> bool {
        self.0.flags.contains(SFlags::BUILTIN_VAMPIRE)
    }

    pub fn is_evaluatable(&self) -> bool {
        self.0.flags.contains(SFlags::EVALUATABLE)
    }

    pub fn as_ptr_usize(&self) -> usize {
        Rc::as_ptr(&self.0) as usize
    }
}
