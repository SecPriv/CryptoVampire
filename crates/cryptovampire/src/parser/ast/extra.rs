use derivative::Derivative;
use utils::string_ref::StrRef;

use super::location::ASTLocation;
use super::{DeclareCell, DeclareFunction, Function, Macro, MacroName, Step, StepName, TypeName};
use crate::error::{LocateHelper, LocationProvider};
use crate::formula::sort::builtins::STEP;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Sub<'str, S> {
    pub span: ASTLocation<'str>,
    pub content: S,
}

impl<'str, T> Sub<'str, T> {
    /// using [Location::default]
    pub fn from_content(c: T) -> Self {
        Self {
            span: Default::default(),
            content: c,
        }
    }
}

impl<'str, T> From<T> for Sub<'str, T> {
    fn from(c: T) -> Self {
        Self::from_content(c)
    }
}

// TODO: change this type. This effectively references the span but copies the
// content. This is the reverse of what we'd likely want.
/// Span and Name
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct SnN<'str, 'b> {
    pub span: &'b ASTLocation<'str>,
    pub name: StrRef<'str>,
}

impl<'str, 'b> SnN<'str, 'b> {
    pub fn span(&self) -> &ASTLocation<'str> {
        self.span
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

impl<'a, 'b, S> From<&'b TypeName<'a, S>> for SnN<'a, 'b>
where
    StrRef<'a>: From<&'b S>,
{
    fn from(value: &'b TypeName<'a, S>) -> Self {
        SnN {
            span: &value.0.span,
            name: value.name().into(),
        }
    }
}

impl<'str, 'b, S> From<&'b Function<'str, S>> for SnN<'str, 'b>
where
    StrRef<'str>: From<&'b S>,
{
    fn from(value: &'b Function<'str, S>) -> Self {
        SnN {
            span: &value.0.span,
            name: value.name().into(),
        }
    }
}

impl<'str, 'b, S> From<&'b StepName<'str, S>> for SnN<'str, 'b>
where
    StrRef<'str>: From<&'b S>,
{
    fn from(value: &'b StepName<'str, S>) -> Self {
        SnN {
            span: &value.0.span,
            name: value.name().into(),
        }
    }
}

impl<'a, 'b, S> From<&'b MacroName<'a, S>> for SnN<'a, 'b>
where
    StrRef<'a>: From<&'b S>,
{
    fn from(value: &'b MacroName<'a, S>) -> Self {
        SnN {
            span: &value.0.span,
            name: value.name().into(),
        }
    }
}

impl<'a, 'b> LocationProvider for SnN<'a, 'b> {
    fn provide(self) -> crate::error::Location {
        self.span.help_provide(&self.name)
    }
}

pub trait AsFunction<'a, 'b> {
    fn name(self) -> SnN<'a, 'b>;
    fn args(self) -> Vec<SnN<'a, 'b>>;
    #[allow(dead_code)]
    fn out(self) -> SnN<'a, 'b>;
}

impl<'a, 'b, S> AsFunction<'a, 'b> for &'b DeclareFunction<'a, S>
where
    StrRef<'a>: From<&'b S>,
{
    fn name(self) -> SnN<'a, 'b> {
        From::from(&self.name)
    }

    fn args(self) -> Vec<SnN<'a, 'b>> {
        self.args.args.iter().map(|tn| tn.into()).collect()
    }

    fn out(self) -> SnN<'a, 'b> {
        From::from(&self.sort)
    }
}

impl<'a, 'b, S> AsFunction<'a, 'b> for &'b DeclareCell<'a, S>
where
    StrRef<'a>: From<&'b S>,
{
    fn name(self) -> SnN<'a, 'b> {
        From::from(&self.name)
    }

    fn args(self) -> Vec<SnN<'a, 'b>> {
        self.args.args.iter().map(|tn| tn.into()).collect()
    }

    fn out(self) -> SnN<'a, 'b> {
        From::from(&self.sort)
    }
}

impl<'a, 'b, S> AsFunction<'a, 'b> for &'b Step<'a, S>
where
    StrRef<'a>: From<&'b S>,
{
    fn name(self) -> SnN<'a, 'b> {
        From::from(&self.name)
    }

    fn args(self) -> Vec<SnN<'a, 'b>> {
        self.args
            .bindings
            .iter()
            .map(|b| From::from(&b.type_name))
            .collect()
    }

    fn out(self) -> SnN<'a, 'b> {
        SnN {
            span: &self.span,
            name: STEP.name(),
        }
    }
}

impl<'a, 'b, S> AsFunction<'a, 'b> for &'b Macro<'a, S>
where
    StrRef<'a>: From<&'b S>,
{
    fn name(self) -> SnN<'a, 'b> {
        From::from(&self.name)
    }

    fn args(self) -> Vec<SnN<'a, 'b>> {
        self.args
            .bindings
            .iter()
            .map(|b| From::from(&b.type_name))
            .collect()
    }

    fn out(self) -> SnN<'a, 'b> {
        panic!()
    }
}
