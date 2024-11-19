use cryptovampire_macros::LocationProvider;
use pest::Span;

use crate::error::Location;

use super::*;

/// [Rule::typed_arguments]
#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypedArgument< S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: Location,
    pub bindings: Vec<VariableBinding<L, S>>,
}
boiler_plate!(@ TypedArgument, 'a, typed_arguments; |p| {
    let span = p.as_span();
    let bindings : Result<Vec<_>, _> = p.into_inner().map(TryInto::try_into).collect();
    Ok(TypedArgument { span, bindings: bindings? })
});

impl<'a,  S> Default for TypedArgument< S> {
    fn default() -> Self {
        Self {
            span: Default::default(),
            bindings: Default::default(),
        }
    }
}

impl<S: Display> Display for TypedArgument< S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})", self.bindings.iter().format(", "))
    }
}

impl< S, U> FromIterator<U> for TypedArgument< S>
where
    VariableBinding< S>: From<U>,
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
#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VariableBinding< S> {
    #[derivative(PartialOrd = "ignore", Ord = "ignore", PartialEq = "ignore")]
    #[provider]
    pub span: Location,
    pub variable: Variable< S>,
    pub type_name: TypeName< S>,
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

impl<'a, S, V, T> From<(V, T)> for VariableBinding<S>
where
    Variable<S>: From<V>,
    TypeName<S>: From<T>,
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

impl<'b, S> IntoIterator for &'b TypedArgument<S> {
    type Item = &'b VariableBinding<S>;

    type IntoIter = Iter<'b, VariableBinding< S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.bindings.iter()
    }
}
