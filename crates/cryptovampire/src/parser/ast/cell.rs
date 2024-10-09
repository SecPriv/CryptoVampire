use cryptovampire_macros::LocationProvider;
use pest::Span;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareCell<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: L,
    pub name: Function<L, S>,
    pub args: DeclareFunctionArgs<L, S>,
    pub sort: TypeName<L, S>,
    pub options: Options<L, S>,
}

boiler_plate!(@ DeclareCell, 'a, declare_cell; |p| {
    let span = p.as_span();
    destruct_rule!(span in [name, args, sort, ?options] = p);
    Ok(Self { span, name, args, sort, options })
});

impl<'a, L, S: Display> Display for DeclareCell<L, S> {
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
impl<L: Default, S> DeclareCell<L, S> {
    pub fn new<TN>(location: L, name: S, args: implvec!(TN), sort: TN) -> Self
    where
        TypeName<L, S>: From<TN>,
    {
        Self {
            span: location,
            name: Function::from_name(name),
            args: DeclareFunctionArgs {
                span: L::default(),
                args: args.into_iter().map_into().collect(),
            },
            sort: sort.into(),
            options: Default::default(),
        }
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignements<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: L,
    pub assignements: Vec<Assignement<L, S>>,
}
boiler_plate!(@ Assignements, 'a, assignements; |p| {
    let span = p.as_span();
    let assignements = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, assignements })
});

impl<L, S: Display> Display for Assignements<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.assignements.iter().format(", "))
    }
}

impl<'a, L: Default, S> FromIterator<Assignement<L, S>> for Assignements<L, S> {
    fn from_iter<T: IntoIterator<Item = Assignement<L, S>>>(iter: T) -> Self {
        Self {
            span: L::default(),
            assignements: iter.into_iter().collect(),
        }
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignement<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: L,
    pub cell: Application<L, S>,
    pub term: Term<L, S>,
    pub fresh_vars: Option<TypedArgument<L, S>>,
}
boiler_plate!(@ Assignement, 'a, assignement; |p| {
    let span = p.as_span();
    let p = p.into_inner().collect_vec();
    // dest_rule!(span in [cell, term] = p);
    match p.len() {
        2 => {
            as_array!(span in [cell, term] = p);
            Ok(Self {
                span,
                cell: cell.try_into().debug_continue()?,
                term: term.try_into().debug_continue()?,
                fresh_vars: None
            })
        }
        3 => {
            as_array!(span in [vars, cell, term] = p);
            Ok(Self {
                span,
                cell: cell.try_into().debug_continue()?,
                term: term.try_into().debug_continue()?,
                fresh_vars: Some(vars.try_into().debug_continue()?)
            })
        }
        _ => unreachable!()
    }

    // Ok(Self { span, cell, term })
});

impl<L, S: Display> Display for Assignement<L, S> {
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
