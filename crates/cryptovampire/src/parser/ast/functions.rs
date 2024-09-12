use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareFunction<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: Function<'a, S>,
    pub args: DeclareFunctionArgs<'a, S>,
    pub sort: TypeName<'a, S>,
    pub options: Options<'a, S>,
}
boiler_plate!(DeclareFunction<'a>, 'a, declare_function; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, args, sort, ?options] = p);
    Ok(Self { span, name, args, sort, options })
});

impl<'a, S> DeclareFunction<'a, S> {
    pub fn name(&self) -> &Ident<'a, S> {
        &self.name.0.content
    }

    pub fn args(&'_ self) -> impl Iterator<Item = &'_ Ident<'a, S>> + '_ {
        self.args.args.iter().map(|tn| &tn.0.content)
    }

    pub fn out(&self) -> &Ident<'a, S> {
        &self.sort.0.content
    }

    pub fn new<TN>(name: S, args: implvec!(TN), sort: TN) -> Self
    where
        TypeName<'a, S>: From<TN>,
    {
        Self {
            span: Default::default(),
            name: Function::from_name(name),
            args: DeclareFunctionArgs {
                span: Default::default(),
                args: args.into_iter().map_into().collect(),
            },
            sort: sort.into(),
            options: Default::default(),
        }
    }
}

impl<'a, S: Display> Display for DeclareFunction<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            args,
            sort,
            options,
            ..
        } = self;
        write!(f, "fun {name}{args}:{sort} {options}")
    }
}

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareFunctionArgs<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub args: Vec<TypeName<'a, S>>,
}
boiler_plate!(DeclareFunctionArgs<'a>, 'a, declare_function_args; |p| {
    let span = p.as_span().into();
    let args = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, args })
});

impl<'a, S: Display> Display for DeclareFunctionArgs<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.is_empty() {
            Ok(())
        } else {
            write!(f, "({})", self.args.iter().format(", "))
        }
    }
}
