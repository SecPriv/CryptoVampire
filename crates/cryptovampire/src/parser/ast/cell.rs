use cryptovampire_macros::LocationProvider;
use location::ASTLocation;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareCell<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub name: Function<'str, S>,
    pub args: DeclareFunctionArgs<'str, S>,
    pub sort: TypeName<'str, S>,
    pub options: Options<'str, S>,
}

boiler_plate!(@ DeclareCell, 'a, declare_cell; |p| {
    let span = p.as_span();
    destruct_rule!(span in [name, args, sort, ?options] = p);
    Ok(Self { span: span.into(), name, args, sort, options })
});

impl<'a, S: Display> Display for DeclareCell<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            args,
            sort,
            options,
            ..
        } = self;
        write!(f, "cell {name}{args}:{sort} {options}")
    }
}

impl<'str, S> DeclareCell<'str, S> {
    pub fn new<TN>(location: ASTLocation<'str>, name: S, args: implvec!(TN), sort: TN) -> Self
    where
        TypeName<'str, S>: From<TN>,
    {
        Self {
            span: location,
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

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignements<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub assignements: Vec<Assignement<'str, S>>,
}
boiler_plate!(@ Assignements, 'a, assignements; |p| {
    let span = p.as_span();
    let assignements = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span:span.into(), assignements })
});

impl<'str, S: Display> Display for Assignements<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.assignements.iter().format(", "))
    }
}

impl<'a, S> FromIterator<Assignement<'a, S>> for Assignements<'a, S> {
    fn from_iter<T: IntoIterator<Item = Assignement<'a, S>>>(iter: T) -> Self {
        Self {
            span: Default::default(),
            assignements: iter.into_iter().collect(),
        }
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignement<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub cell: Application<'str, S>,
    pub term: Term<'str, S>,
    pub fresh_vars: Option<TypedArgument<'str, S>>,
}

boiler_plate!(@ Assignement, 'a, assignement; |p| {
    let span = p.as_span();
    let p = p.into_inner().collect_vec();
    // dest_rule!(span in [cell, term] = p);
    match p.len() {
        2 => {
            as_array!(span in [cell, term] = p);
            Ok(Self {
                span:span.into(),
                cell: cell.try_into().debug_continue()?,
                term: term.try_into().debug_continue()?,
                fresh_vars: None
            })
        }
        3 => {
            as_array!(span in [vars, cell, term] = p);
            Ok(Self {
                span:span.into(),
                cell: cell.try_into().debug_continue()?,
                term: term.try_into().debug_continue()?,
                fresh_vars: Some(vars.try_into().debug_continue()?)
            })
        }
        _ => unreachable!()
    }

    // Ok(Self { span, cell, term })
});

impl<'str, S: Display> Display for Assignement<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            cell,
            term,
            fresh_vars,
            ..
        } = self;
        if let Some(fv) = fresh_vars {
            write!(f, "{fv} ")?;
        }
        write!(f, "{cell} <- {term}")
    }
}
