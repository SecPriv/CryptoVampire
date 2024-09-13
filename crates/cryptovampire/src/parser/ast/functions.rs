use pest::Span;

use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareFunction<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub name: Function<L, S>,
    pub args: DeclareFunctionArgs<L, S>,
    pub sort: TypeName<L, S>,
    pub options: Options<L, S>,
}
boiler_plate!(DeclareFunction<Span<'a>, &'a str>, 'a, declare_function; |p| {
    let span = p.as_span();
    destruct_rule!(span in [name, args, sort, ?options] = p);
    Ok(Self { span, name, args, sort, options })
});

impl<L, S> DeclareFunction<L, S> {
    pub fn name(&self) -> &Ident<L, S> {
        &self.name.0.content
    }

    pub fn args(&'_ self) -> impl Iterator<Item = &'_ Ident<L, S>> + '_ {
        self.args.args.iter().map(|tn| &tn.0.content)
    }

    pub fn out(&self) -> &Ident<L, S> {
        &self.sort.0.content
    }

    pub fn new<TN>(location: L, name: S, args: implvec!(TN), sort: TN) -> Self
    where
        TypeName<L, S>: From<TN>,
        L: Clone + Default,
    {
        Self {
            span: location.clone(),
            name: Function::from_name(name),
            args: DeclareFunctionArgs {
                span: location.clone(),
                args: args.into_iter().map_into().collect(),
            },
            sort: sort.into(),
            options: Default::default(),
        }
    }
}

impl<'a, L, S: Display> Display for DeclareFunction<L, S> {
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
pub struct DeclareFunctionArgs<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub args: Vec<TypeName<L, S>>,
}
boiler_plate!(DeclareFunctionArgs<Span<'a>, &'a str>, 'a, declare_function_args; |p| {
    let span = p.as_span();
    let args = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, args })
});

impl<'a, L, S: Display> Display for DeclareFunctionArgs<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.is_empty() {
            Ok(())
        } else {
            write!(f, "({})", self.args.iter().format(", "))
        }
    }
}
