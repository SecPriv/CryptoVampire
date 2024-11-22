use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareType<'str, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: ASTLocation<'str>,
    pub name: TypeName<'str, S>,
    pub options: Options<'str, S>,
}
boiler_plate!(@ DeclareType, 'a, declare_type; |p| {
    let span = p.as_span();
    destruct_rule!(span in [name, ?options] = p);
    Ok(Self { span:span.into(), name, options })
});

impl<'str, S> DeclareType<'str, S> {
    pub fn name(&self) -> &S {
        self.name.name()
    }

    pub fn name_span(&self) -> &ASTLocation<'str> {
        &self.name.0.span
    }

    pub fn new(name: TypeName<'str, S>) -> Self {
        Self {
            span: Default::default(),
            name,
            options: Default::default(),
        }
    }
}

impl<'str, S: Display> Display for DeclareType<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { name, options, .. } = self;
        write!(f, "type {name} {options}")
    }
}
