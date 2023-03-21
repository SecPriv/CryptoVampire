pub mod builtins;
// pub mod collection;
pub mod sorted;
use bitflags::bitflags;
use bumpalo::{collections, Bump};
use core::fmt::Debug;
use std::{
    cmp::Ordering,
    fmt::Display,
    hash::{Hash, Hasher},
    rc::{Rc, Weak},
};

bitflags! {
    #[derive(Default )]
    pub struct SFlags: u32 {
        const TERM_ALGEBRA =        1<<0;
        const BUILTIN_VAMPIRE =     1<<1;
        const EVALUATABLE =         1<<2;
    }
}

// pub type AsSort = AsRef<InnerSort>;

#[derive(Debug, Clone, Copy)]
pub struct Sort<'bump> {
    inner: &'bump InnerSort<'bump>,
}

// #[derive(Debug, Clone)]
// pub struct RcSort(Rc<InnerSort>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerSort<'bump> {
    inner: HiddenSort<'bump>,
}

impl<'bump> InnerSort<'bump> {
    fn new(bump: &'bump Bump, name: &str, flags: SFlags) -> &'bump mut Self {
        bump.alloc(InnerSort {
            inner: HiddenSort {
                name: collections::String::from_str_in(name, bump),
                flags,
            },
        })
    }

    pub fn as_sort<'sort>(&'sort self) -> Sort<'sort> {
        Sort { inner: self }
    }
}

// enum ISort {
//     BuiltIn(&'static IISort),
//     Dynamic(Rc<IISort>),
// }

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct HiddenSort<'bump> {
    name: collections::String<'bump>,
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

// impl<'a> From<&'a str> for RcSort {
//     fn from(value: &'a str) -> Self {
//         Self::new(value.to_owned(), Default::default())
//     }
// }

// impl<'a> From<&'a str> for Sort {
//     fn from(str: &'a str) -> Self {
//         Self::new(str)
//     }
// }

impl<'a> Display for Sort<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_ref().name)
    }
}

// impl Display for RcSort {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         self.as_sort().fmt(f)
//     }
// }

impl<'a> Hash for Sort<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ptr_usize().hash(state);
    }
}

impl<'a> Sort<'a> {
    // pub fn new(str: &str) -> Self {
    //     Self::new_with_flag(str, Default::default())
    // }
    // pub fn new_with_flag(str: &str, flags: SFlags) -> Self {
    //     Sort(ISort::Dynamic(Rc::new(ISort {
    //         name: str.to_owned(),
    //         flags,
    //     })))
    // }

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
        self.as_ref() as *const HiddenSort as usize
    }

    // pub fn as_rc(&self) -> RcSort {
    //     self.0.itself.upgrade().unwrap() // cannot fail so long as self id a valid reference
    // }
}

impl<'a> AsRef<HiddenSort<'a>> for Sort<'a> {
    fn as_ref(&self) -> &HiddenSort {
        // match self.0 {
        //     ISort::BuiltIn(ref s) => s,
        //     ISort::Dynamic(ref s) => s.as_ref(),
        // }
        self.0
    }
}

// impl RcSort {
//     // pub fn as_sort<'a>(&'a self) -> Sort<'a> {
//     //     Sort(self.0.as_ref())
//     // }

//     pub fn new(name: String, flags: SFlags) -> Self {
//         RcSort(Rc::new_cyclic(|itself| InnerSort {
//             inner: HiddenSort {
//                 name,
//                 flags,
//                 itself: Weak::clone(itself),
//             },
//         }))
//     }

//     pub fn as_sort<'a>(&'a self) -> Sort<'a> {
//         Sort(self.0.as_ref())
//     }
// }

// impl Eq for RcSort {}
// impl Ord for RcSort {
//     fn cmp(&self, other: &Self) -> Ordering {
//         self.as_sort().cmp(&other.as_sort())
//     }
// }
// impl PartialEq for RcSort {
//     fn eq(&self, other: &Self) -> bool {
//         self.as_sort() == other.as_sort()
//     }
// }
// impl PartialOrd for RcSort {
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//         self.as_sort().partial_cmp(&other.as_sort())
//     }
// }
// impl Hash for RcSort {
//     fn hash<H: Hasher>(&self, state: &mut H) {
//         self.as_sort().hash(state);
//     }
// }

impl<'bump> AsRef<HiddenSort<'bump>> for InnerSort<'bump> {
    fn as_ref(&self) -> &HiddenSort<'bump> {
        &self.inner
    }
}

// impl<'a> AsRef<InnerSort<'a>> for Sort<'a> {
//     fn as_ref(&self) -> &InnerSort {
//         self.inner
//     }
// }
