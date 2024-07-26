use std::{
    any::type_name,
    borrow::{Borrow, Cow},
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
    ops::Deref,
    sync::Arc,
};

#[cfg(feature = "serde")]
use serde::{de::Visitor, Deserialize, Serialize};

#[cfg(feature = "serde")]
pub use validator::{ValidationError, Validator, TrivialValidator};

pub type CRc = Arc<str>;

/// A boxed string that can also be a `&str`
pub struct StrRef<'a, V = TrivialValidator> {
    validator: PhantomData<V>,
    inner: Inner<'a>,
}

#[derive(Debug, Clone)]
enum Inner<'a> {
    Borrowed(&'a str),
    Owned(CRc),
}

impl<'a, V> StrRef<'a, V> {
    pub fn is_borrowed(&self) -> bool {
        matches!(self.inner, Inner::Borrowed(_))
    }
    pub fn is_owned(&self) -> bool {
        matches!(self.inner, Inner::Owned(_))
    }

    pub fn into_owned<'b>(self) -> StrRef<'b, V>
    where
        V: 'b,
    {
        match self.inner {
            Inner::Borrowed(b) => StrRef {
                validator: Default::default(),
                inner: Inner::Owned(b.into()),
            },
            Inner::Owned(o) => StrRef {
                validator: Default::default(),
                inner: Inner::Owned(o),
            },
        }
    }

    pub fn as_str(&self) -> &str {
        self.as_ref()
    }

    pub fn drop_guard(self) -> StrRef<'a> {
        let Self { inner, .. } = self;
        StrRef {
            validator: Default::default(),
            inner,
        }
    }
}
impl<'a, V: Validator> StrRef<'a, V> {
    pub fn new_owned<U>(v: U) -> Result<Self, ValidationError>
    where
        CRc: From<U>,
    {
        let i: CRc = v.into();
        if V::validate(i.as_ref()) {
            Ok(StrRef {
                validator: Default::default(),
                inner: Inner::Owned(i),
            })
        } else {
            Err(ValidationError)
        }
    }

    pub fn new_borrowed(v: &'a str) -> Result<Self, ValidationError> {
        if V::validate(v) {
            Ok(StrRef {
                validator: Default::default(),
                inner: Inner::Borrowed(v),
            })
        } else {
            Err(ValidationError)
        }
    }
}

impl<'a, T> PartialEq for StrRef<'a, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}
impl<'a, T> Eq for StrRef<'a, T> {}
impl<'a, T> PartialOrd for StrRef<'a, T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_ref(), other.as_ref())
    }
}
impl<'a, V> Ord for StrRef<'a, V> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(self.as_ref(), other.as_ref())
    }
}
impl<'a, V> Hash for StrRef<'a, V> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ref().hash(state)
    }
}

impl<'a, V: Validator> From<&'a str> for StrRef<'a, V> {
    #[inline]
    fn from(value: &'a str) -> Self {
        Self::new_borrowed(value).unwrap()
    }
}

impl<'a, 'b, V: Validator> From<&'b &'a str> for StrRef<'b, V> {
    #[inline]
    fn from(value: &'b &'a str) -> Self {
        Self::new_borrowed(value).unwrap()
    }
}

impl<'a> From<String> for StrRef<'a> {
    #[inline]
    fn from(value: String) -> Self {
        Self::new_owned(value.into_boxed_str()).unwrap()
        // Self::Owned(value.into_boxed_str().into())
    }
}

impl<'a> From<Box<str>> for StrRef<'a> {
    #[inline]
    fn from(value: Box<str>) -> Self {
        // Self::Owned(value.into())
        Self::new_owned(value).unwrap()
    }
}

impl<'a> From<Cow<'a, str>> for StrRef<'a> {
    fn from(value: Cow<'a, str>) -> Self {
        match value {
            Cow::Borrowed(s) => s.into(),
            Cow::Owned(s) => s.into(),
        }
    }
}

impl<'a, T> AsRef<str> for StrRef<'a, T> {
    #[inline]
    fn as_ref(&self) -> &str {
        match &self.inner {
            Inner::Borrowed(s) => *s,
            Inner::Owned(s) => s.as_ref(),
        }
    }
}

impl<'a, V> Into<Arc<str>> for StrRef<'a, V> {
    #[inline]
    fn into(self) -> Arc<str> {
        match self.inner {
            Inner::Borrowed(s) => Arc::from(s),
            Inner::Owned(s) => s,
        }
    }
}

impl<'a, V> Into<String> for StrRef<'a, V> {
    #[inline]
    fn into(self) -> String {
        Box::from(self).to_string()
    }
}

impl<'a, V> Into<Box<str>> for StrRef<'a, V> {
    fn into(self) -> Box<str> {
        <Self as Into<String>>::into(self).into_boxed_str()
    }
}

impl<'a, V> Deref for StrRef<'a, V> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a, V> Borrow<str> for StrRef<'a, V> {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_ref()
    }
}

impl<'a, V> Display for StrRef<'a, V> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self.as_str(), f)
    }
}

impl<'a, V> hashbrown::Equivalent<String> for StrRef<'a, V> {
    #[inline]
    fn equivalent(&self, key: &String) -> bool {
        self.as_ref() == key.as_str()
    }
}

impl<'a, V> Clone for StrRef<'a, V> {
    fn clone(&self) -> Self {
        Self {
            validator: Default::default(),
            inner: self.inner.clone(),
        }
    }
}

impl<'a, V> Debug for StrRef<'a, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let val = type_name::<V>();
        let menum = match &self.inner {
            Inner::Borrowed(_) => "Borrowed",
            Inner::Owned(_) => "Owned",
        };
        f.debug_tuple(&format!("StrRef<{val}>::{menum}"))
            .field(&self.to_string())
            .finish()
    }
}

#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct StrRefVisistor<V>(PhantomData<V>);

#[cfg(feature = "serde")]
impl<V: Validator> Default for StrRefVisistor<V> {
    fn default() -> Self {
        StrRefVisistor(Default::default())
    }
}

#[cfg(feature = "serde")]
impl<'a, V> Visitor<'a> for StrRefVisistor<V>
where
    V: Validator,
{
    type Value = StrRef<'a, V>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            formatter,
            "a string formatted according to {}::validate()",
            type_name::<V>()
        )
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        self.visit_string(String::from(v))
    }

    fn visit_borrowed_str<E>(self, v: &'a str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        StrRef::new_borrowed(v).map_err(E::custom)
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        StrRef::new_owned(v.into_boxed_str()).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'a, 'de: 'a , V: Validator> Deserialize<'de> for StrRef<'a, V> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_str(StrRefVisistor::default())
    }
}

#[cfg(feature = "serde")]
impl<'a, V> Serialize for StrRef<'a, V> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_ref())
    }
}

mod validator {
    use thiserror::Error;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Error, Default)]
    #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
    #[error("validation error")]
    pub struct ValidationError;

    pub trait Validator {
        fn validate(str: &str) -> bool;
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
    pub struct TrivialValidator;
    impl Validator for TrivialValidator {
        #[inline]
        fn validate(_: &str) -> bool {
            true
        }
    }
}
