use cryptovampire_macros::LocationProvider;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareType<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: L,
    pub name: TypeName<L, S>,
    pub options: Options<L, S>,
}
boiler_plate!(@ DeclareType, 'a, declare_type; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, ?options] = p);
    Ok(Self { span, name, options })
});

impl<L, S> DeclareType<L, S> {
    pub fn name(&self) -> &S {
        self.name.name()
    }

    pub fn name_span(&self) -> &L {
        &self.name.0.span
    }

    pub fn new(name: TypeName<L, S>) -> Self
    where
        L: Default,
    {
        Self {
            span: Default::default(),
            name,
            options: Default::default(),
        }
    }
}

impl<L, S: Display> Display for DeclareType<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { name, options, .. } = self;
        write!(f, "type {name} {options}")
    }
}
