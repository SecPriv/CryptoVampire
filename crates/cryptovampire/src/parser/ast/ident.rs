use cryptovampire_macros::LocationProvider;
use location::{ASTLocation, AsASTLocation};

use super::*;
use crate::error::{LocateHelper, Location};
use crate::formula::utils::Applicable;

/// [Rule::ident]
#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Ident<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub content: S,
}
boiler_plate!(@ Ident, 's, ident; |p| {
Ok(Ident { span: p.as_span().into(), content: p.as_str()})
});

impl<'str, S> Ident<'str, S> {
    pub fn name(&self) -> &S {
        &self.content
    }
}

impl<'str, S> Ident<'str, S> {
    pub fn from_content(s: S) -> Self {
        Ident {
            span: Default::default(),
            content: s,
        }
    }
}

impl<'str, S: Display> Display for Ident<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'str, S> From<S> for Ident<'str, S> {
    fn from(value: S) -> Self {
        Self::from_content(value)
    }
}

/// [Rule::type_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypeName<'str, S>(pub Sub<'str, Ident<'str, S>>);
boiler_plate!(TypeName<'a, &'a str>, 'a, type_name; |p| {
    Ok(Self(Sub { span: p.as_span().into(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'str, S> TypeName<'str, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn name_span(&self) -> &ASTLocation<'str> {
        &self.0.span
    }
}
impl<'str, S: Display> Display for TypeName<'str, S> {
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
pub struct MacroName<'str, S>(pub Sub<'str, Ident<'str, S>>);
boiler_plate!(MacroName<'a, &'a str>, 'a, macro_name; |p| {
    Ok(Self(Sub { span: p.ast_location(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'str, S> MacroName<'str, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn span(&self) -> &ASTLocation<'str> {
        &self.0.span
    }
}

impl<'str, S: Display> Display for MacroName<'str, S> {
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
pub struct Function<'str, S>(pub Sub<'str, Ident<'str, S>>);
boiler_plate!(Function<'a, &'a str>, 'a, function; |p| {
    Ok(Self(Sub { span: p.ast_location(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'str, S> Function<'str, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }

    pub fn span(&self) -> &ASTLocation<'str> {
        &self.0.span
    }
}
impl<'str, S> Function<'str, S> {
    pub fn from_name(s: S) -> Self {
        Self(Sub::from_content(Ident::from_content(s)))
    }
}

impl<'str, S: Display> Display for Function<'str, S> {
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
pub struct Variable<'str, S>(pub Sub<'str, S>);
boiler_plate!(Variable<'a, &'a str>, 'a, variable; |p| {
    Ok(Self(Sub { span: p.ast_location(), content: p.as_str() }))
});

impl<'str, S> Variable<'str, S> {
    pub fn name(&self) -> &S {
        &self.0.content
    }
}

impl<'str, S: Display> Display for Variable<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'str, S> From<S> for Variable<'str, S> {
    fn from(value: S) -> Self {
        Variable(value.into())
    }
}

/// [Rule::step_name]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct StepName<'str, S>(pub Sub<'str, Ident<'str, S>>);
boiler_plate!(StepName<'a, &'a str>, 'a, step_name; |p| {
    Ok(Self(Sub { span: p.ast_location(), content: p.into_inner().next().unwrap().try_into()? }))
});

impl<'str, S> StepName<'str, S> {
    pub fn name(&self) -> &S {
        self.0.content.name()
    }
}
impl<'str, S> StepName<'str, S> {
    pub fn from_s(s: S) -> Self {
        Self(Sub {
            span: Default::default(),
            content: Ident::from_content(s),
        })
    }
}

impl<'str, S: Display> Display for StepName<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl<'str, S> From<S> for StepName<'str, S> {
    fn from(value: S) -> Self {
        StepName(Ident::from_content(value).into())
    }
}

macro_rules! mk_location_provider {
    ($name:ident) => {
        impl<'a, 'str, S: std::fmt::Debug> crate::error::LocationProvider for &'a $name<'str, S>
        where
            S: std::fmt::Display,
        {
            fn provide(self) -> Location {
                self.0.span.help_provide(&self)
            }
        }
    };
}
mk_location_provider!(Function);
mk_location_provider!(MacroName);
mk_location_provider!(StepName);
mk_location_provider!(Variable);
