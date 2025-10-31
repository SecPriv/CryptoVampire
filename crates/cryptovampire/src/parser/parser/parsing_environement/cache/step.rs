use std::sync::Arc;

use itertools::izip;

use crate::formula::formula::ARichFormula;
use crate::formula::function::Function;
use crate::formula::function::builtin::INPUT;
use crate::formula::manipulation::{FrozenSubst, FrozenSubstF, OneVarSubst, OneVarSubstF};
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::MESSAGE;
use crate::formula::utils::Applicable;
use crate::formula::variable::{Variable, uvar};
use crate::parser::parser::parsable_trait::VarProxy;
use crate::parser::{FromStaticString, ast};
use crate::problem::step::Step;

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

impl<'bump, S: Clone> From<NamedVariable<'bump, S>> for (S, VarProxy<'bump>) {
    fn from(val: NamedVariable<'bump, S>) -> Self {
        let NamedVariable { name, variable } = val;
        (name.clone(), variable.into())
    }
}

impl<'bump, S> From<NamedVariable<'bump, S>> for Variable<'bump> {
    fn from(val: NamedVariable<'bump, S>) -> Self {
        val.variable()
    }
}
