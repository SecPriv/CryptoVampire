use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareType<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: TypeName<'a, S>,
    pub options: Options<'a, S>,
}
boiler_plate!(DeclareType<'a>, 'a, declare_type; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, ?options] = p);
    Ok(Self { span, name, options })
});

impl<'a, S> DeclareType<'a, S> {
    pub fn name(&self) -> &S {
        self.name.name()
    }

    pub fn name_span(&self) -> &Location<'a> {
        &self.name.0.span
    }

    pub fn new(name: TypeName<'a, S>) -> Self {
        Self {
            span: Default::default(),
            name,
            options: Default::default(),
        }
    }
}

impl<'a, S: Display> Display for DeclareType<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { name, options, .. } = self;
        write!(f, "type {name} {options}")
    }
}
