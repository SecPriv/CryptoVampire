use pest::Span;

use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Options<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub options: Vec<MOption<L, S>>,
}

impl<L: Default, S> Default for Options<L, S> {
    fn default() -> Self {
        Self {
            span: Default::default(),
            options: Default::default(),
        }
    }
}

impl<L, S: Display> Display for Options<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.options.iter().format(", "))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MOption<L, S>(Ident<L, S>);

impl<L, S> From<Ident<L, S>> for MOption<L, S> {
    fn from(value: Ident<L, S>) -> Self {
        Self(value)
    }
}

boiler_plate!(Options<Span<'a>, &'a str>, 'a, options; |p| {
    let span = p.as_span();
    let options = p.into_inner().map(Ident::try_from).map(|r| r.map(MOption::from)).try_collect()?;
    Ok(Self { span, options })
});
impl<L, S> Options<L, S> {
    pub fn empty(span: L) -> Self {
        Self {
            span,
            options: Default::default(),
        }
    }

    pub fn as_str_list<'b>(&'b self) -> impl Iterator<Item = &'_ S> + 'b {
        self.options.iter().map(|MOption(i)| &i.content)
    }

    pub fn iter<'b>(&'b self) -> <&'b Self as IntoIterator>::IntoIter {
        (&self).into_iter()
    }
    pub fn contains(&self, str: &str) -> bool
    where
        S: Borrow<str>,
    {
        self.as_str_list().any(|s| s.borrow() == str)
    }
}

impl<L, S: Display> Display for MOption<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'b, L, S> IntoIterator for &'b Options<L, S> {
    type Item = &'b MOption<L, S>;

    type IntoIter = slice::Iter<'b, MOption<L, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.options.iter()
    }
}

impl<'a, S> FromIterator<S> for Options<(), S> {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        iter.into_iter()
            .map(Ident::from)
            .map(MOption::from)
            .collect()
    }
}

impl<L: Default, S> FromIterator<MOption<L, S>> for Options<L, S> {
    fn from_iter<T: IntoIterator<Item = MOption<L, S>>>(iter: T) -> Self {
        Options {
            span: Default::default(),
            options: iter.into_iter().collect(),
        }
    }
}
