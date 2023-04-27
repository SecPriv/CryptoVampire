use std::{ops::Deref, fmt::Display};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum StrRef<'a> {
    Ref(&'a str),
    Owned(Box<str>),
}

impl<'a> From<&'a str> for StrRef<'a> {
    fn from(value: &'a str) -> Self {
        StrRef::Ref(value)
    }
}

impl<'a> From<String> for StrRef<'a> {
    fn from(value: String) -> Self {
        Self::Owned(value.into_boxed_str())
    }
}

impl<'a> From<Box<str>> for StrRef<'a> {
    fn from(value: Box<str>) -> Self {
        Self::Owned(value)
    }
}

impl<'a> AsRef<str> for StrRef<'a> {
    fn as_ref(&self) -> &str {
        match self {
            StrRef::Ref(s) => *s,
            StrRef::Owned(s) => s.as_ref(),
        }
    }
}

impl<'a> Deref for StrRef<'a> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a> Display for StrRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_ref().fmt(f)
    }
}