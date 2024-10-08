use cryptovampire_lib::formula::sort::builtins::STEP;
use derivative::Derivative;
use utils::string_ref::StrRef;

use super::{
    error::Location, DeclareCell, DeclareFunction, Function, Macro, MacroName, Step, StepName,
    TypeName,
};

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Sub<'s, T> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'s>,
    pub content: T,
}

impl<'s, T> Sub<'s, T> {
    /// using [Location::default]
    pub fn from_content(c: T) -> Self {
        Self {
            span: Default::default(),
            content: c,
        }
    }
}

impl<'s, T> From<T> for Sub<'s, T> {
    fn from(c: T) -> Self {
        Self::from_content(c)
    }
}

/// Span and Name
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct SnN<'a, 'b> {
    pub span: &'b Location<'a>,
    pub name: StrRef<'a>,
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

impl<'a, 'b, S> From<&'b Function<'a, S>> for SnN<'a, 'b>
where
    StrRef<'a>: From<&'b S>,
{
    fn from(value: &'b Function<'a, S>) -> Self {
        SnN {
            span: &value.0.span,
            name: value.name().into(),
        }
    }
}

impl<'a, 'b, S> From<&'b StepName<'a, S>> for SnN<'a, 'b>
where
    StrRef<'a>: From<&'b S>,
{
    fn from(value: &'b StepName<'a, S>) -> Self {
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
