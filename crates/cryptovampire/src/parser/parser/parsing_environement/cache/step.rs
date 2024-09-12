use std::sync::Arc;

use crate::parser::{ast, parser::parsable_trait::VarProxy, FromStaticString};
use crate::{
    formula::{
        formula::ARichFormula,
        function::{builtin::INPUT, Function},
        manipulation::{FrozenSubst, FrozenSubstF, OneVarSubst, OneVarSubstF},
        sort::{builtins::MESSAGE, Sort},
        utils::Applicable,
        variable::{uvar, Variable},
    },
    problem::step::Step,
};
use itertools::izip;

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct StepCache<'str, 'bump, S> {
    pub args: Arc<[Sort<'bump>]>,
    pub args_name: Arc<[S]>,
    pub ast: &'str ast::Step<'str, S>,
    pub function: Function<'bump>,
    pub step: Step<'bump>,
}

/// convenient struct to model named arguments
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct NamedVariable<'bump, S> {
    pub name: S,
    pub variable: Variable<'bump>,
}

impl<'str, 'bump, S> StepCache<'str, 'bump, S>
where
    S: Clone + FromStaticString,
{
    pub fn args_vars(&self) -> impl Iterator<Item = NamedVariable<'bump, S>> + '_ {
        izip!(0.., self.args.iter(), self.args_name.iter()).map(|(id, sort, name)| NamedVariable {
            name: name.clone(),
            variable: Variable { id, sort: *sort },
        })
    }

    /// all the [NamedVariable] that should be visible within a [ast::Step]
    pub fn args_vars_with_input(&self) -> impl Iterator<Item = NamedVariable<'bump, S>> + '_ {
        self.args_vars().chain([self.input_named_var()])
    }

    /// the special `in` variable
    pub fn input_named_var(&self) -> NamedVariable<'bump, S> {
        NamedVariable {
            name: S::from_static("in"),
            variable: Variable {
                id: self.args.len().try_into().unwrap(),
                sort: MESSAGE.as_sort(),
            },
        }
    }

    pub fn substitution_input(&self) -> OneVarSubstF<'bump> {
        OneVarSubst {
            id: self.input_named_var().id(),
            f: INPUT.f([self.function.f(self.args_vars().map(|v| v.variable))]),
        }
    }

    pub fn substitution(&self, args: &[ARichFormula<'bump>]) -> FrozenSubstF<'_, 'bump> {
        assert_eq!(args.len(), self.args.len());

        let vars = self.args_vars_with_input().map(|v| v.id()).collect();
        let formulas = args
            .iter()
            .cloned()
            .chain([INPUT.f([self.function.f(args)])])
            .collect();

        FrozenSubst::new(vars, formulas)
    }
}

impl<'bump, S> NamedVariable<'bump, S> {
    pub fn variable(&self) -> Variable<'bump> {
        self.variable
    }

    #[allow(dead_code)]
    pub fn name(&self) -> &S {
        &self.name
    }

    #[allow(dead_code)]
    pub fn sort(&self) -> Sort<'bump> {
        self.variable.sort
    }

    pub fn id(&self) -> uvar {
        self.variable.id
    }
}

impl<'str, 'bump, S: Clone> Into<(S, VarProxy<'bump>)> for NamedVariable<'bump, S> {
    fn into(self) -> (S, VarProxy<'bump>) {
        let NamedVariable { name, variable } = self;
        (name.clone(), variable.into())
    }
}

impl<'bump, S> Into<Variable<'bump>> for NamedVariable<'bump, S> {
    fn into(self) -> Variable<'bump> {
        self.variable()
    }
}
