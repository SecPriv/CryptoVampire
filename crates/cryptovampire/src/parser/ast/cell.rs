use cryptovampire_macros::LocationProvider;
use pest::Span;

use crate::error::Location;

use super::*;

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareCell< S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: Location,
    pub name: Function< S>,
    pub args: DeclareFunctionArgs< S>,
    pub sort: TypeName< S>,
    pub options: Options< S>,
}

boiler_plate!(@ DeclareCell, 'a, declare_cell; |p| {
    let span = p.as_span();
    destruct_rule!(span in [name, args, sort, ?options] = p);
    Ok(Self { span, name, args, sort, options })
});

impl<'a,  S: Display> Display for DeclareCell<S> {
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
impl< S> DeclareCell< S> {
    pub fn new<TN>(location: Location, name: S, args: implvec!(TN), sort: TN) -> Self
    where
        TypeName< S>: From<TN>,
    {
        Self {
            span: location,
            name: Function::from_name(name),
            args: DeclareFunctionArgs {
                span: Location::from_locate(()),
                args: args.into_iter().map_into().collect(),
            },
            sort: sort.into(),
            options: Default::default(),
        }
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignements< S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: Location,
    pub assignements: Vec<Assignement< S>>,
}
boiler_plate!(@ Assignements, 'a, assignements; |p| {
    let span = p.as_span();
    let assignements = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, assignements })
});

impl< S: Display> Display for Assignements< S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.assignements.iter().format(", "))
    }
}

impl<'a, S> FromIterator<Assignement<S>> for Assignements< S> {
    fn from_iter<T: IntoIterator<Item = Assignement<S>>>(iter: T) -> Self {
        Self {
            span: L::default(),
            assignements: iter.into_iter().collect(),
        }
    }
}

#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignement< S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: Location,
    pub cell: Application< S>,
    pub term: Term<S>,
    pub fresh_vars: Option<TypedArgument< S>>,
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

impl< S: Display> Display for Assignement< S> {
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
