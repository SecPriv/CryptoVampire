use bitflags::bitflags;
use core::fmt::Debug;
use std::{cmp::Ordering, fmt::Display, hash::Hash, rc::Rc};

bitflags! {
    #[derive(Default )]
    pub struct SFlags: u32 {
        const TERM_ALGEBRA =        1<<0;
        const BUILTIN_VAMPIRE =     1<<1;
        const EVALUATABLE =         1<<2;
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Sort<'a>(&'a ISort);

// enum ISort {
//     BuiltIn(&'static IISort),
//     Dynamic(Rc<IISort>),
// }

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct ISort {
    name: String,
    flags: SFlags,
}

impl<'a> PartialEq for Sort<'a> {
    fn eq(&self, other: &Self) -> bool {
        // Arc::ptr_eq(&self.0, &other.0)
        // self.0.name == other.0.name
        std::ptr::eq(self.as_ref(), other.as_ref())
    }
}

impl<'a> Eq for Sort<'a> {}

impl<'a> Ord for Sort<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Ord::cmp(&Rc::as_ptr(&self.0), &Rc::as_ptr(&other.0))
        if self != other {
            Ord::cmp(self.name(), other.name())
                .then(Ord::cmp(&self.as_ptr_usize(), &self.as_ptr_usize()))
        } else {
            Ordering::Equal
        }
    }
}

impl<'a> PartialOrd for Sort<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

// impl Clone for Sort {
//     fn clone(&self) -> Self {
//         // Self(Rc::clone(&self.0))
//         match &self.0 {
//             ISort::BuiltIn(s) => Sort(ISort::BuiltIn(s)),
//             ISort::Dynamic(s) => Sort(ISort::Dynamic(Rc::clone(s))),
//         }
//     }
// }

impl<'a> From<&'a str> for Sort {
    fn from(str: &'a str) -> Self {
        Self::new(str)
    }
}

impl<'a> Display for Sort<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_ref().name)
    }
}

impl<'a> Hash for Sort<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ptr_usize().hash(state);
    }
}

impl<'a> Sort<'a> {
    pub fn new(str: &str) -> Self {
        Self::new_with_flag(str, Default::default())
    }
    pub fn new_with_flag(str: &str, flags: SFlags) -> Self {
        Sort(ISort::Dynamic(Rc::new(ISort {
            name: str.to_owned(),
            flags,
        })))
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
        self.as_ref() as *const ISort as usize
    }
}

impl<'a> AsRef<ISort> for Sort<'a> {
    fn as_ref(&self) -> &ISort {
        // match self.0 {
        //     ISort::BuiltIn(ref s) => s,
        //     ISort::Dynamic(ref s) => s.as_ref(),
        // }
        self.0
    }
}
