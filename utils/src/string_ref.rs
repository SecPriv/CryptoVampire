use std::{borrow::Borrow, fmt::Display, hash::Hash, ops::Deref, sync::Arc};

#[derive(Debug, Clone)]
/// A boxed string that can also be a `&str`
pub enum StrRef<'a> {
    Ref(&'a str),
    Owned(Arc<str>),
}

impl<'a> PartialEq for StrRef<'a> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}
impl<'a> Eq for StrRef<'a> {}
impl<'a> PartialOrd for StrRef<'a> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_ref(), other.as_ref())
    }
}
impl<'a> Ord for StrRef<'a> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(self.as_ref(), other.as_ref())
    }
}
impl<'a> Hash for StrRef<'a> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ref().hash(state)
    }
}

impl<'a> StrRef<'a> {
    #[inline]
    pub fn into_owned(self) -> Arc<str> {
        self.into()
    }

    #[inline]
    pub fn into_string(self) -> String {
        self.into_owned().as_ref().into()
    }
}

impl<'a> From<&'a str> for StrRef<'a> {
    #[inline]
    fn from(value: &'a str) -> Self {
        StrRef::Ref(value)
    }
}

impl<'a> From<String> for StrRef<'a> {
    #[inline]
    fn from(value: String) -> Self {
        Self::Owned(value.into_boxed_str().into())
    }
}

impl<'a> From<Box<str>> for StrRef<'a> {
    #[inline]
    fn from(value: Box<str>) -> Self {
        Self::Owned(value.into())
    }
}

impl<'a> AsRef<str> for StrRef<'a> {
    #[inline]
    fn as_ref(&self) -> &str {
        match self {
            StrRef::Ref(s) => *s,
            StrRef::Owned(s) => s.as_ref(),
        }
    }
}

impl<'a> Into<Arc<str>> for StrRef<'a> {
    #[inline]
    fn into(self) -> Arc<str> {
        match self {
            StrRef::Ref(s) => Arc::from(s),
            StrRef::Owned(s) => s,
        }
    }
}

impl<'a> Into<String> for StrRef<'a> {
    #[inline]
    fn into(self) -> String {
        Box::from(self).into_string()
    }
}

impl<'a> Deref for StrRef<'a> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a> Borrow<str> for StrRef<'a> {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_ref()
    }
}

impl<'a> Display for StrRef<'a> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl<'a> hashbrown::Equivalent<String> for StrRef<'a> {
    #[inline]
    fn equivalent(&self, key: &String) -> bool {
        self.as_ref() == key.as_str()
    }
}
