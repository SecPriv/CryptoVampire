use super::*;

/// [Rule::typed_arguments]
#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypedArgument<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub bindings: Vec<VariableBinding<'a, S>>,
}
boiler_plate!(TypedArgument<'a>, 'a, typed_arguments; |p| {
    let span = p.as_span().into();
    let bindings : Result<Vec<_>, _> = p.into_inner().map(TryInto::try_into).collect();
    Ok(TypedArgument { span, bindings: bindings? })
});

impl<'a, S> Default for TypedArgument<'a, S> {
    fn default() -> Self {
        Self {
            span: Default::default(),
            bindings: Default::default(),
        }
    }
}

impl<'a, S: Display> Display for TypedArgument<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})", self.bindings.iter().format(", "))
    }
}

impl<'a, S, U> FromIterator<U> for TypedArgument<'a, S>
where
    VariableBinding<'a, S>: From<U>,
{
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        let bindings = iter.into_iter().map_into().collect();
        Self {
            span: Default::default(),
            bindings,
        }
    }
}

/// [Rule::variable_binding]
#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VariableBinding<'a, S = &'a str> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore")]
    pub span: Location<'a>,
    pub variable: Variable<'a, S>,
    pub type_name: TypeName<'a, S>,
}
boiler_plate!(VariableBinding<'s>, 's, variable_binding; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [variable, type_name] = p.into_inner());
    Ok(VariableBinding{span, variable, type_name})
});

impl<'a, S: Display> Display for VariableBinding<'a, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", &self.variable, &self.type_name)
    }
}

impl<'a, S, V, T> From<(V, T)> for VariableBinding<'a, S>
where
    Variable<'a, S>: From<V>,
    TypeName<'a, S>: From<T>,
{
    fn from((variable, type_name): (V, T)) -> Self {
        let variable = variable.into();
        let type_name = type_name.into();
        Self {
            span: Default::default(),
            variable,
            type_name,
        }
    }
}

impl<'a, 'b, S> IntoIterator for &'b TypedArgument<'a, S> {
    type Item = &'b VariableBinding<'a, S>;

    type IntoIter = Iter<'b, VariableBinding<'a, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.bindings.iter()
    }
}
