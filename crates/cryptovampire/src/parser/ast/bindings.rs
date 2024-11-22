use cryptovampire_macros::LocationProvider;
use location::{ASTLocation, AsASTLocation};

use super::*;

/// [Rule::typed_arguments]
#[derive(Derivative, LocationProvider)]
#[derivative(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypedArgument<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub bindings: Vec<VariableBinding<'str, S>>,
}
boiler_plate!(@ TypedArgument, 'a, typed_arguments; |p| {
    let span = p.ast_location();
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

impl<'str, S: Display> Display for TypedArgument<'str, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})", self.bindings.iter().format(", "))
    }
}

impl<'str, S, U> FromIterator<U> for TypedArgument<'str, S>
where
    VariableBinding<'str, S>: From<U>,
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
pub struct VariableBinding<'str, S> {
    #[provider]
    pub span: ASTLocation<'str>,
    pub variable: Variable<'str, S>,
    pub type_name: TypeName<'str, S>,
}
boiler_plate!(@ VariableBinding, 's, variable_binding; |p| {
    let span = p.as_span();
    destruct_rule!(span in [variable, type_name] = p.into_inner());
    Ok(VariableBinding{span: span.into(), variable, type_name})
});

impl<'str, S: Display> Display for VariableBinding<'str, S> {
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

impl<'b, 'str, S> IntoIterator for &'b TypedArgument<'str, S> {
    type Item = &'b VariableBinding<'str, S>;

    type IntoIter = Iter<'b, VariableBinding<'str, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.bindings.iter()
    }
}
