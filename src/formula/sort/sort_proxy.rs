//! A way to emulate sort variables for type inference

use std::{cell::RefCell, default, fmt::Display, rc::Rc};
use thiserror::Error;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Error)]
pub enum InferenceError<'bump> {
    #[error("can't infer a sort")]
    CantInfer { proxy: SortProxy<'bump> },
    #[error("sort mismatch: (expected {}, got {})", .expected.name(), .recieved.name())]
    SortMismatch {
        proxy: SortProxy<'bump>,
        expected: Sort<'bump>,
        recieved: Sort<'bump>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Error)]
pub enum UpdateError {
    #[error("the sort is read only")]
    ReadOnly,
    #[error("was set before")]
    AlreadySet,
}

use super::Sort;
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum SortProxy<'bump> {
    Var(Rc<RefCell<Option<Sort<'bump>>>>),
    Static(Sort<'bump>),
}

impl<'bump> Default for SortProxy<'bump> {
    fn default() -> Self {
        Self::Var(Default::default())
    }
}

impl<'bump> SortProxy<'bump> {
    /// Check or set that `self` is `s`.
    ///
    /// The error is set up so that is expects `self` to be `s`
    pub fn expects<'a>(&self, s: Sort<'bump>) -> Result<(), InferenceError<'bump>> {
        match self.as_option() {
            Some(s2) if s2 == s => Ok(()),
            None => {
                // if not defined yet, assign a sort
                self.set(s).unwrap(); // cannot fail
                Ok(())
            }
            // Some(s2) => err(merr!(span; "wrong sort: {} instead of {}", s2.name(), s.name())),
            Some(s2) => Err(InferenceError::SortMismatch {
                proxy: self.clone(),
                expected: s,
                recieved: s2,
            }),
        }
    }

    /// Check or set that `s` is `self`.
    ///
    /// The error is set up so that is expects `s` to be `self`
    pub fn matches<'a>(&self, s: Sort<'bump>) -> Result<(), InferenceError<'bump>> {
        match self.expects(s) {
            Err(InferenceError::SortMismatch {
                proxy,
                expected,
                recieved,
            }) => Err(InferenceError::SortMismatch {
                proxy,
                expected: recieved,
                recieved: expected,
            }),
            x => x,
        }
    }

    pub fn matches_sort(s1: Sort<'bump>, s2: Sort<'bump>) -> Result<(), InferenceError<'bump>> {
        Self::from(s1).matches(s2)
    }

    pub fn unify<'a>(&self, other: &Self) -> Result<Sort<'bump>, InferenceError<'bump>> {
        match (self.into(), other.into()) {
            (Some(s), Some(s2)) => {
                if s == s2 {
                    Ok(s)
                } else {
                    // err(merr!(span; "wrong sort: got {} expected {}", s.name(), s2.name()))
                    Err(InferenceError::SortMismatch {
                        proxy: self.clone(),
                        expected: s2,
                        recieved: s,
                    })
                }
            }
            (None, Some(s2)) => {
                self.set(s2).unwrap(); // cannot fail
                Ok(s2)
            }
            (Some(s), None) => {
                other.set(s).unwrap(); // cannot fail
                Ok(s)
            }
            // _ => err(merr!(span; "can't infer sort")),
            _ => Err(InferenceError::CantInfer {
                proxy: self.clone(),
            }),
        }
    }

    pub fn set(&self, sort: Sort<'bump>) -> Result<&Self, UpdateError> {
        // *RefCell::borrow_mut(&self.0.as_ref()) = Some(sort);
        match self {
            SortProxy::Var(v) => {
                let mut v = v.borrow_mut();
                match v.as_ref() {
                    Some(_) => Err(UpdateError::AlreadySet),
                    None => {
                        *v = Some(sort);
                        Ok(self)
                    }
                }
            }
            SortProxy::Static(_) => Err(UpdateError::ReadOnly),
        }
    }

    pub fn as_option(&self) -> Option<Sort<'bump>> {
        self.into()
    }
}

impl<'bump> From<Sort<'bump>> for SortProxy<'bump> {
    #[inline]
    fn from(value: Sort<'bump>) -> Self {
        Self::Static(value)
    }
}
impl<'bump, 'a> From<&'a Sort<'bump>> for SortProxy<'bump> {
    #[inline]
    fn from(value: &'a Sort<'bump>) -> Self {
        Self::from(*value)
    }
}

impl<'bump> Into<Option<Sort<'bump>>> for SortProxy<'bump> {
    #[inline]
    fn into(self) -> Option<Sort<'bump>> {
        (&self).into()
    }
}

impl<'bump, 'a> Into<Option<Sort<'bump>>> for &'a SortProxy<'bump> {
    fn into(self) -> Option<Sort<'bump>> {
        match self {
            SortProxy::Var(v) => v.borrow().clone(),
            SortProxy::Static(s) => Some(*s),
        }
    }
}

impl<'bump> Display for SortProxy<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SortProxy::Var(v) => match v.borrow().as_ref() {
                Some(s) => write!(f, "{}", s),
                None => write!(f, "_{}", v.as_ptr() as usize),
            },
            SortProxy::Static(s) => write!(f, "${}", s),
        }
    }
}
