use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Options<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub options: Vec<MOption<'a, S>>,
}

impl<'a, S> Default for Options<'a, S> {
    fn default() -> Self {
        Self {
            span: Default::default(),
            options: Default::default(),
        }
    }
}

impl<'a, S: Display> Display for Options<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.options.iter().format(", "))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MOption<'a, S = &'a str>(Ident<'a, S>);

impl<'a, S> From<Ident<'a, S>> for MOption<'a, S> {
    fn from(value: Ident<'a, S>) -> Self {
        Self(value)
    }
}

boiler_plate!(Options<'a>, 'a, options; |p| {
    let span = p.as_span().into();
    let options = p.into_inner().map(Ident::try_from).map(|r| r.map(MOption::from)).try_collect()?;
    Ok(Self { span, options })
});
impl<'a, S> Options<'a, S> {
    pub fn empty(span: Location<'a>) -> Self {
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

impl<'a, S: Display> Display for MOption<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, 'b, S> IntoIterator for &'b Options<'a, S> {
    type Item = &'b MOption<'a, S>;

    type IntoIter = slice::Iter<'b, MOption<'a, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.options.iter()
    }
}
