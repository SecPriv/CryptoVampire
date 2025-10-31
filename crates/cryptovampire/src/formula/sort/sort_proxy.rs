//! A way to emulate sort variables for type inference

use std::cell::RefCell;
use std::fmt::Display;
use std::rc::Rc;

use thiserror::Error;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Error)]
pub enum InferenceError {
    #[error("can't infer a sort {0}")]
    CantInfer(Box<str>),
    #[error("sort mismatch in {proxy}: (expected {expected}, got {recieved})")]
    SortMismatch {
        proxy: Box<str>,
        expected: Box<str>,
        recieved: Box<str>,
    },
    #[error(transparent)]
    UpdateError(#[from] UpdateError),
}

impl InferenceError {
    /// the what is expected and what was recieved
    pub fn flip(self) -> Self {
        match self {
            InferenceError::SortMismatch {
                proxy,
                expected,
                recieved,
            } => InferenceError::SortMismatch {
                proxy,
                expected: recieved,
                recieved: expected,
            },
            _ => self,
        }
    }

    pub fn mismach<'bump>(
        proxy: &SortProxy<'bump>,
        expected: Sort<'bump>,
        recieved: Sort<'bump>,
    ) -> Self {
        Self::SortMismatch {
            proxy: proxy.to_string().into_boxed_str(),
            expected: expected.name().into(),
            recieved: recieved.name().into(),
        }
    }

    pub fn cant_infer(source: &SortProxy<'_>) -> Self {
        Self::CantInfer(source.to_string().into_boxed_str())
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Error)]
pub enum UpdateError {
    #[error("the sort is read only")]
    ReadOnly,
    #[error("was set before")]
    AlreadySet,
}

use super::Sort;
use crate::environement::traits::{KnowsRealm, Realm};
#[derive(Debug, Clone)]
pub enum SortProxy<'bump> {
    Var(Rc<RefCell<Option<Sort<'bump>>>>),
    Static(Sort<'bump>),
}

impl<'bump> SortProxy<'bump> {
    pub fn is_known(&self) -> bool {
        self.as_option().is_some()
    }

    /// Check or set that `self` is `s`.
    ///
    /// The error is set up so that it expects `self` to be `s`
    pub fn expects(&self, s: Sort<'bump>, realm: &impl KnowsRealm) -> Result<(), InferenceError> {
        match self.as_option() {
            Some(s2) if Sort::eq_realm(&s2, &s, realm) => Ok(()),
            None => {
                // if not defined yet, assign a sort
                self.set(s).unwrap(); // cannot fail
                Ok(())
            }
            // Some(s2) => err(merr!(span; "wrong sort: {} instead of {}", s2.name(), s.name())),
            Some(s2) => Err(InferenceError::mismach(self, s, s2)),
        }
    }

    /// Check or set that `s` is `self`.
    ///
    /// The error is set up so that is expects `s` to be `self`
    pub fn matches(&self, s: Sort<'bump>, realm: &impl KnowsRealm) -> Result<(), InferenceError> {
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
    ) -> Result<(), InferenceError> {
        Self::matches(&s1.into(), s2, realm)
    }

    /// unifies two [`SortProxies`](SortProxy) and set them
    ///
    /// The error is returned as if `self` is expected to be `other`
    pub fn unify(
        &self,
        other: &Self,
        realm: &impl KnowsRealm,
    ) -> Result<Sort<'bump>, InferenceError> {
        match (self.into(), other.into()) {
            (Some(s), Some(s2)) => {
                if Sort::eq_realm(&s, &s2, realm) {
                    Ok(s)
                } else {
                    Err(InferenceError::mismach(self, s2, s))
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
            _ => Err(InferenceError::cant_infer(self)),
        }
    }

    pub fn unify_rev(
        &self,
        other: &Self,
        realm: &impl KnowsRealm,
    ) -> Result<Sort<'bump>, InferenceError> {
        self.unify(other, realm).map_err(|err| err.flip())
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

    /// check is `self` is already set to `other`
    ///
    /// similar to `maches` or `expect` but without modifying `self`
    pub fn is_sort(&self, other: Sort<'bump>) -> bool {
        self.as_option() == Some(other)
    }

    pub fn realm(&self) -> Option<Realm> {
        self.as_option().and_then(|s| s.realm())
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

impl<'bump> From<SortProxy<'bump>> for Option<Sort<'bump>> {
    #[inline]
    fn from(val: SortProxy<'bump>) -> Self {
        (&val).into()
    }
}

impl<'bump, 'a> From<&'a SortProxy<'bump>> for Option<Sort<'bump>> {
    fn from(val: &'a SortProxy<'bump>) -> Self {
        match val {
            SortProxy::Var(v) => *v.borrow(),
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
