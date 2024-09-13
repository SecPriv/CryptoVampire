use pest::Span;

use crate::formula::utils::Applicable;

use super::*;

/// [Rule::ident]
#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Ident<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub content: S,
}
boiler_plate!(@ Ident, 's, ident; |p| {
Ok(Ident { span: p.as_span().into(), content: p.as_str()})
});

impl<L, S> Ident<L, S> {
    pub fn name(&self) -> &S {
        &self.content
    }
}

impl<L: Default, S> Ident<L, S> {
    pub fn from_content(s: S) -> Self {
        Ident {
            span: L::default(),
            content: s,
        }
    }
}

impl<L, S: Display> Display for Ident<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<S> From<S> for Ident<(), S> {
    fn from(value: S) -> Self {
        Self::from_content(value)
    }
}

/// [Rule::type_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypeName<L, S>(pub Sub<L, Ident<L, S>>);
boiler_plate!(TypeName<Span<'a>, &'a str>, 'a, type_name; |p| {
Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<L, S> TypeName<L, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn name_span(&self) -> &L {
        &self.0.span
    }
}
impl<'a, L, S: Display> Display for TypeName<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for TypeName<(), S> {
    fn from(value: S) -> Self {
        TypeName(Sub::from(Ident::from(value)))
    }
}

/// [Rule::macro_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MacroName<L, S>(pub Sub<L, Ident<L, S>>);
boiler_plate!(MacroName<Span<'a>, &'a str>, 'a, macro_name; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<L, S> MacroName<L, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn span(&self) -> &L {
        &self.0.span
    }
}

impl<'a, L, S: Display> Display for MacroName<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}!", self.name())
    }
}

impl<'a, S> From<S> for MacroName<(), S> {
    fn from(value: S) -> Self {
        MacroName(Sub::from(Ident::from(value)))
    }
}

/// [Rule::function]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Function<L, S>(pub Sub<L, Ident<L, S>>);
boiler_plate!(Function<Span<'a>, &'a str>, 'a, function; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<L, S> Function<L, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn span(&self) -> &L {
        &self.0.span
    }
}
impl<L: Default, S> Function<L, S> {
    pub fn from_name(s: S) -> Self {
        Self(Sub::from_content(Ident::from_content(s)))
    }
}

impl<'a, L, S: Display> Display for Function<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, 'b, S: Clone + Borrow<str>> Applicable for &'b Function<(), S> {
    type Term = ast::Term<(), S>;

    fn f<U, I>(self, args: I) -> Self::Term
    where
        I: IntoIterator<Item = U>,
        Self::Term: From<U>,
    {
        match Operation::get_operation(self.name().borrow()) {
            Some(op) => op.apply(args.into_iter().map_into()),
            None => ast::Application::Application {
                span: Default::default(),
                function: Function::clone(self),
                args: args.into_iter().map_into().collect(),
            }
            .into(),
        }
    }
}

/// [Rule::variable]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Variable<L, S>(pub Sub<L, S>);
boiler_plate!(Variable<Span<'a>, &'a str>, 'a, variable; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.as_str() }))
});

impl<L, S> Variable<L, S> {
    pub fn name(&self) -> &S {
        &self.0.content
    }
}

impl<'a, L, S: Display> Display for Variable<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<S> From<S> for Variable<(), S> {
    fn from(value: S) -> Self {
        Variable(value.into())
    }
}
/// [Rule::step_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct StepName<L, S>(pub Sub<L, Ident<L, S>>);
boiler_plate!(StepName<Span<'a>, &'a str>, 'a, step_name; |p| {
    Ok(Self(Sub { span: p.as_span(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<L, S> StepName<L, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }
}
impl<S> StepName<(), S> {
    pub fn from_s(s: S) -> Self {
        Self(Sub {
            span: Default::default(),
            content: Ident::from_content(s),
        })
    }
}

impl<'a, L, S: Display> Display for StepName<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<S> From<S> for StepName<(), S> {
    fn from(value: S) -> Self {
        StepName(Ident::from_content(value).into())
    }
}
