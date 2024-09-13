use pest::Span;

use super::*;

/// [Rule::typed_arguments]
#[derive(Derivative)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypedArgument<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub bindings: Vec<VariableBinding<L, S>>,
}
boiler_plate!(@ TypedArgument, 'a, typed_arguments; |p| {
    let span = p.as_span();
    let bindings : Result<Vec<_>, _> = p.into_inner().map(TryInto::try_into).collect();
    Ok(TypedArgument { span, bindings: bindings? })
});

impl<'a, L: Default, S> Default for TypedArgument<L, S> {
    fn default() -> Self {
        Self {
            span: Default::default(),
            bindings: Default::default(),
        }
    }
}

impl<L, S: Display> Display for TypedArgument<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})", self.bindings.iter().format(", "))
    }
}

impl<L: Default, S, U> FromIterator<U> for TypedArgument<L, S>
where
    VariableBinding<L, S>: From<U>,
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
pub struct VariableBinding<L, S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    pub span: L,
    pub variable: Variable<L, S>,
    pub type_name: TypeName<L, S>,
}
boiler_plate!(@ VariableBinding, 's, variable_binding; |p| {
    let span = p.as_span().into();
    destruct_rule!(span in [variable, type_name] = p.into_inner());
    Ok(VariableBinding{span, variable, type_name})
});

impl<'a, L, S: Display> Display for VariableBinding<L, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", &self.variable, &self.type_name)
    }
}

impl<'a, L: Default, S, V, T> From<(V, T)> for VariableBinding<L, S>
where
    Variable<L, S>: From<V>,
    TypeName<L, S>: From<T>,
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

impl<'b, S, L> IntoIterator for &'b TypedArgument<L, S> {
    type Item = &'b VariableBinding<L, S>;

    type IntoIter = Iter<'b, VariableBinding<L, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.bindings.iter()
    }
}
