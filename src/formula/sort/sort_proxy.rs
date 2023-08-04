//! A way to emulate sort variables for type inference

use std::{cell::RefCell, fmt::Display, rc::Rc};
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

use crate::environement::traits::KnowsRealm;

use super::Sort;
#[derive(Debug, Clone)]
pub enum SortProxy<'bump> {
    Var(Rc<RefCell<Option<Sort<'bump>>>>),
    Static(Sort<'bump>),
}

impl<'bump> SortProxy<'bump> {
    /// Check or set that `self` is `s`.
    ///
    /// The error is set up so that it expects `self` to be `s`
    pub fn expects<'a>(
        &self,
        s: Sort<'bump>,
        realm: &impl KnowsRealm,
    ) -> Result<(), InferenceError<'bump>> {
        match self.as_option() {
            Some(s2) if Sort::eq_realm(&s2, &s, realm) => Ok(()),
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
    pub fn matches<'a>(
        &self,
        s: Sort<'bump>,
        realm: &impl KnowsRealm,
    ) -> Result<(), InferenceError<'bump>> {
        match self.expects(s, realm) {
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

    pub fn matches_sort(
        s1: Sort<'bump>,
        s2: Sort<'bump>,
        realm: &impl KnowsRealm,
    ) -> Result<(), InferenceError<'bump>> {
        Self::matches(&s1.into(), s2, realm)
    }

    pub fn unify<'a>(
        &self,
        other: &Self,
        realm: &impl KnowsRealm,
    ) -> Result<Sort<'bump>, InferenceError<'bump>> {
        match (self.into(), other.into()) {
            (Some(s), Some(s2)) => {
                if Sort::eq_realm(&s, &s2, realm) {
                    Ok(s)
                } else {
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

    pub fn as_owned(&self) -> Option<Self> {
        self.as_option().map(Into::into)
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

impl<'bump> Default for SortProxy<'bump> {
    fn default() -> Self {
        Self::Var(Default::default())
    }
}

impl<'bump> PartialEq for SortProxy<'bump> {
    fn eq(&self, other: &Self) -> bool {
        self.as_option() == other.as_option()
    }
}

impl<'bump> Eq for SortProxy<'bump> {}

impl<'bump> PartialOrd for SortProxy<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl<'bump> Ord for SortProxy<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&self.as_option(), &other.as_option())
    }
}
