use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;
use crate::error::{LocateHelper, Location};

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Options<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub options: Vec<MOption<'str, S>>,
}

impl<'str, S> Default for Options<'str, S> {
    fn default() -> Self {
        Self {
            span: Default::default(),
            options: Default::default(),
        }
    }
}

impl<'str, S: Display> Display for Options<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.options.iter().format(", "))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MOption<'str, S>(Ident<'str, S>);

impl<'str, S> From<Ident<'str, S>> for MOption<'str, S> {
    fn from(value: Ident<'str, S>) -> Self {
        Self(value)
    }
}

boiler_plate!(Options<'a, &'a str>, 'a, options; |p| {
    let span = p.as_span();
    let options = p.into_inner().map(Ident::try_from).map(|r| r.map(MOption::from)).try_collect()?;
    Ok(Self { span:span.into(), options })
});

impl<'str, S> Options<'str, S> {
    pub fn empty(span: ASTLocation<'str>) -> Self {
        Self {
            span,
            options: Default::default(),
        }
    }

    #[allow(clippy::needless_lifetimes)]
    pub fn as_str_list<'b>(&'b self) -> impl Iterator<Item = &'_ S> + 'b {
        self.options.iter().map(|MOption(i)| &i.content)
    }

    pub fn iter(&self) -> <&Self as IntoIterator>::IntoIter {
        self.into_iter()
    }

    pub fn contains(&self, str: &str) -> bool
    where
        S: Borrow<str>,
    {
        self.as_str_list().any(|s| s.borrow() == str)
    }
}

impl<'str, S: Display> Display for MOption<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'str, S> crate::error::LocationProvider for MOption<'str, S>
where
    S: std::fmt::Display + std::fmt::Debug,
{
    fn provide(self) -> Location {
        self.0.span.help_provide(&self)
    }
}

impl<'b, 'str, S> IntoIterator for &'b Options<'str, S> {
    type Item = &'b MOption<'str, S>;

    type IntoIter = slice::Iter<'b, MOption<'str, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.options.iter()
    }
}

impl<'a, S> FromIterator<S> for Options<'a, S> {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        iter.into_iter()
            .map(Ident::from)
            .map(MOption::from)
            .collect()
    }
}

impl<'str, S> FromIterator<MOption<'str, S>> for Options<'str, S> {
    fn from_iter<T: IntoIterator<Item = MOption<'str, S>>>(iter: T) -> Self {
        Options {
            span: Default::default(),
            options: iter.into_iter().collect(),
        }
    }
}
