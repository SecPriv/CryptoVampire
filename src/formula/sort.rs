use core::fmt::Debug;
use std::{fmt::Display, sync::Arc};

#[derive(Hash)]
pub struct Sort(Arc<InnerSort>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct InnerSort {
    name: String,
}

impl Debug for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl PartialEq for Sort {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Sort {}

impl Ord for Sort {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&Arc::as_ptr(&self.0), &Arc::as_ptr(&other.0))
    }
}

impl PartialOrd for Sort {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl Clone for Sort {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
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
        Sort(Arc::new(InnerSort {
            name: str.to_owned(),
        }))
    }
}
