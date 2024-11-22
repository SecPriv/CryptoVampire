use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareFunction<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub name: Function<'str, S>,
    pub args: DeclareFunctionArgs<'str, S>,
    pub sort: TypeName<'str, S>,
    pub options: Options<'str, S>,
}
boiler_plate!(DeclareFunction<'a, &'a str>, 'a, declare_function; |p| {
    let span = p.as_span();
    destruct_rule!(span in [name, args, sort, ?options] = p);
    Ok(Self { span: span.into(), name, args, sort, options })
});

impl<'str, S> DeclareFunction<'str, S> {
    pub fn name(&self) -> &Ident<'str, S> {
        &self.name.0.content
    }

    pub fn args(&'_ self) -> impl Iterator<Item = &'_ Ident<'str, S>> + '_ {
        self.args.args.iter().map(|tn| &tn.0.content)
    }

    pub fn out(&self) -> &Ident<'str, S> {
        &self.sort.0.content
    }

    pub fn new<TN>(location: ASTLocation<'str>, name: S, args: implvec!(TN), sort: TN) -> Self
    where
        TypeName<'str, S>: From<TN>,
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

impl<'str, S: Display> Display for DeclareFunction<'str, S> {
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

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareFunctionArgs<'str, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: ASTLocation<'str>,
    pub args: Vec<TypeName<'str, S>>,
}
boiler_plate!(DeclareFunctionArgs<'a, &'a str>, 'a, declare_function_args; |p| {
    let span = p.as_span();
    let args = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span: span.into(), args })
});

impl<'str, S: Display> Display for DeclareFunctionArgs<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.is_empty() {
            Ok(())
        } else {
            write!(f, "({})", self.args.iter().format(", "))
        }
    }
}
