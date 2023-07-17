use std::{fmt::Display, hash::Hash, ops::Deref};

#[derive(Debug, Clone)]
/// A boxed string that can also be a `&str`
pub enum StrRef<'a> {
    Ref(&'a str),
    Owned(Box<str>),
}

impl<'a> PartialEq for StrRef<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}
impl<'a> Eq for StrRef<'a> {}
impl<'a> PartialOrd for StrRef<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_ref(), other.as_ref())
    }
}
impl<'a> Ord for StrRef<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(self.as_ref(), other.as_ref())
    }
}
impl<'a> Hash for StrRef<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ref().hash(state)
    }
}

impl<'a> StrRef<'a> {
    pub fn into_owned(self) -> Box<str> {
        match self {
            StrRef::Ref(s) => Box::from(s),
            StrRef::Owned(s) => s,
        }
    }

    pub fn into_string(self) -> String {
        self.into_owned().into_string()
    }
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

impl<'a> Into<Box<str>> for StrRef<'a> {
    fn into(self) -> Box<str> {
        match self {
            StrRef::Ref(s) => Box::from(s),
            StrRef::Owned(s) => s,
        }
    }
}

impl<'a> Into<String> for StrRef<'a> {
    fn into(self) -> String {
        Box::from(self).into_string()
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
