use cryptovampire_lib::formula::utils::Applicable;

use super::*;

/// [Rule::ident]
#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Ident<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub content: S,
}
boiler_plate!(Ident<'s>, 's, ident; |p| {
Ok(Ident { span: p.as_span().into(), content: p.as_str()})
});

impl<'s, S> Ident<'s, S> {
    pub fn name(&self) -> &S {
        &self.content
    }

    /// using [Location::default]
    pub fn from_content(s: S) -> Self {
        Ident {
            span: Default::default(),
            content: s,
        }
    }
}

impl<'a, S: Display> Display for Ident<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for Ident<'a, S> {
    fn from(value: S) -> Self {
        Self::from_content(value)
    }
}

/// [Rule::type_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypeName<'a, S = &'a str>(pub Sub<'a, Ident<'a, S>>);
boiler_plate!(TypeName<'a>, 'a, type_name; |p| {
Ok(Self(Sub { span: p.as_span().into(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a, S> TypeName<'a, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn name_span(&self) -> Location<'a> {
        self.0.span
    }
}
impl<'a, S: Display> Display for TypeName<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for TypeName<'a, S> {
    fn from(value: S) -> Self {
        TypeName(Sub::from(Ident::from(value)))
    }
}

/// [Rule::macro_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MacroName<'a, S = &'a str>(pub Sub<'a, Ident<'a, S>>);
boiler_plate!(MacroName<'a>, 'a, macro_name; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a, S> MacroName<'a, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn span(&self) -> Location<'a> {
        self.0.span
    }
}

impl<'a, S: Display> Display for MacroName<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}!", self.name())
    }
}

impl<'a, S> From<S> for MacroName<'a, S> {
    fn from(value: S) -> Self {
        MacroName(Sub::from(Ident::from(value)))
    }
}

/// [Rule::function]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Function<'a, S = &'a str>(pub Sub<'a, Ident<'a, S>>);
boiler_plate!(Function<'a>, 'a, function; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a, S> Function<'a, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn span(&self) -> Location<'a> {
        self.0.span
    }

    pub fn from_name(s: S) -> Self {
        Self(Sub::from_content(Ident::from_content(s)))
    }
}

impl<'a, S: Display> Display for Function<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, 'b, S: Clone + Borrow<str>> Applicable for &'b Function<'a, S> {
    type Term = ast::Term<'a, S>;

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
pub struct Variable<'a, S = &'a str>(pub Sub<'a, S>);
boiler_plate!(Variable<'a>, 'a, variable; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.as_str() }))
});

impl<'a, S> Variable<'a, S> {
    pub fn name(&self) -> &S {
        &self.0.content
    }
}

impl<'a, S: Display> Display for Variable<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for Variable<'a, S> {
    fn from(value: S) -> Self {
        Variable(value.into())
    }
}
/// [Rule::step_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct StepName<'a, S = &'a str>(pub Sub<'a, Ident<'a, S>>);
boiler_plate!(StepName<'a>, 'a, step_name; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'a, S> StepName<'a, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn from_s(s: S) -> Self {
        Self(Sub {
            span: Default::default(),
            content: Ident::from_content(s),
        })
    }
}

impl<'a, S: Display> Display for StepName<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'a, S> From<S> for StepName<'a, S> {
    fn from(value: S) -> Self {
        StepName(Ident::from_content(value).into())
    }
}
