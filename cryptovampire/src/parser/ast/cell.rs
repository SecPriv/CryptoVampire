use super::*;

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct DeclareCell<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub name: Function<'a, S>,
    pub args: DeclareFunctionArgs<'a, S>,
    pub sort: TypeName<'a, S>,
    pub options: Options<'a, S>,
}

boiler_plate!(DeclareCell<'a>, 'a, declare_cell; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [name, args, sort, ?options] = p);
    Ok(Self { span, name, args, sort, options })
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
impl<'a, S> DeclareCell<'a, S> {
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

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignements<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub assignements: Vec<Assignement<'a, S>>,
}
boiler_plate!(Assignements<'a>, 'a, assignements; |p| {
    let span = p.as_span().into();
    let assignements = p.into_inner().map(TryInto::try_into).try_collect()?;
    Ok(Self { span, assignements })
});

impl<'a, S: Display> Display for Assignements<'a, S> {
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

#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Assignement<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub cell: Application<'a, S>,
    pub term: Term<'a, S>,
    pub fresh_vars: Option<TypedArgument<'a, S>>,
}
boiler_plate!(Assignement<'a>, 'a, assignement; |p| {
let span = p.as_span().into();
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

impl<'a, S: Display> Display for Assignement<'a, S> {
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
