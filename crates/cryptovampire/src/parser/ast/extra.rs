use crate::formula::sort::builtins::STEP;
use derivative::Derivative;
use utils::string_ref::StrRef;

use super::{
     DeclareCell, DeclareFunction, Function, Macro, MacroName, Step, StepName,
    TypeName,
};

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Sub<L, T> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub content: T,
}

impl<L: Default, T> Sub<L, T> {
    /// using [Location::default]
    pub fn from_content(c: T) -> Self {
        Self {
            span: L::default(),
            content: c,
        }
    }
}

impl<L: Default, T> From<T> for Sub<L, T> {
    fn from(c: T) -> Self {
        Self::from_content(c)
    }
}

/// Span and Name
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct SnN<'a, 'b, L> {
    pub span: &'b L,
    pub name: StrRef<'a>,
}

impl<'a, 'b, S, L> From<&'b TypeName<L, S>> for SnN<'a, 'b, L>
where
    StrRef<'a>: From<&'b S>,
{
    fn from(value: &'b TypeName<L, S>) -> Self {
        SnN {
            span: &value.0.span,
            name: value.name().into(),
        }
    }
}

impl<'a, 'b, S, L> From<&'b Function<L, S>> for SnN<'a, 'b, L>
where
    StrRef<'a>: From<&'b S>,
{
    fn from(value: &'b Function<L, S>) -> Self {
        SnN {
            span: &value.0.span,
            name: value.name().into(),
        }
    }
}

impl<'a, 'b, L, S> From<&'b StepName<L, S>> for SnN<'a, 'b, L>
where
    StrRef<'a>: From<&'b S>,
{
    fn from(value: &'b StepName<L, S>) -> Self {
        SnN {
            span: &value.0.span,
            name: value.name().into(),
        }
    }
}

impl<'a, 'b, L, S> From<&'b MacroName<L, S>> for SnN<'a, 'b, L>
where
    StrRef<'a>: From<&'b S>,
{
    fn from(value: &'b MacroName<L, S>) -> Self {
        SnN {
            span: &value.0.span,
            name: value.name().into(),
        }
    }
}

pub trait AsFunction<'a, 'b, L> {
    fn name(self) -> SnN<'a, 'b, L>;
    fn args(self) -> Vec<SnN<'a, 'b, L>>;
    #[allow(dead_code)]
    fn out(self) -> SnN<'a, 'b, L>;
}

impl<'a, 'b, S, L> AsFunction<'a, 'b, L> for &'b DeclareFunction<L, S>
where
    StrRef<'a>: From<&'b S>,
{
    fn name(self) -> SnN<'a, 'b, L> {
        From::from(&self.name)
    }

    fn args(self) -> Vec<SnN<'a, 'b, L>> {
        self.args.args.iter().map(|tn| tn.into()).collect()
    }

    fn out(self) -> SnN<'a, 'b, L> {
        From::from(&self.sort)
    }
}

impl<'a, 'b, L, S> AsFunction<'a, 'b, L> for &'b DeclareCell<L, S>
where
    StrRef<'a>: From<&'b S>,
{
    fn name(self) -> SnN<'a, 'b, L> {
        From::from(&self.name)
    }

    fn args(self) -> Vec<SnN<'a, 'b, L>> {
        self.args.args.iter().map(|tn| tn.into()).collect()
    }

    fn out(self) -> SnN<'a, 'b, L> {
        From::from(&self.sort)
    }
}

impl<'a, 'b, S, L> AsFunction<'a, 'b, L> for &'b Step<L, S>
where
    StrRef<'a>: From<&'b S>,
{
    fn name(self) -> SnN<'a, 'b, L> {
        From::from(&self.name)
    }

    fn args(self) -> Vec<SnN<'a, 'b, L>> {
        self.args
            .bindings
            .iter()
            .map(|b| From::from(&b.type_name))
            .collect()
    }

    fn out(self) -> SnN<'a, 'b, L> {
        SnN {
            span: &self.span,
            name: STEP.name(),
        }
    }
}

impl<'a, 'b, S, L> AsFunction<'a, 'b, L> for &'b Macro<L, S>
where
    StrRef<'a>: From<&'b S>,
{
    fn name(self) -> SnN<'a, 'b, L> {
        From::from(&self.name)
    }

    fn args(self) -> Vec<SnN<'a, 'b, L>> {
        self.args
            .bindings
            .iter()
            .map(|b| From::from(&b.type_name))
            .collect()
    }

    fn out(self) -> SnN<'a, 'b, L> {
        panic!()
    }
}
