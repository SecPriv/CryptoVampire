use std::sync::Arc;

use itertools::Itertools;

use crate::{
    formula::{
        formula::ARichFormula,
        function::{builtin::INPUT, Function},
        manipulation::{FrozenSubst, FrozenSubstF, OneVarSubst, OneVarSubstF, Substitution},
        sort::{builtins::MESSAGE, Sort},
        variable::Variable,
    },
    parser::{ast, parser::parsable_trait::VarProxy},
    problem::step::Step,
};

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct StepCache<'str, 'bump> {
    pub args: Arc<[Sort<'bump>]>,
    pub args_name: Arc<[&'str str]>,
    pub ast: &'str ast::Step<'str>,
    pub function: Function<'bump>,
    pub step: Step<'bump>,
}

/// convenient struct to model named arguments
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct NamedVariable<'str, 'bump> {
    pub name: &'str str,
    pub variable: Variable<'bump>,
}

impl<'str, 'bump> StepCache<'str, 'bump> {
    pub fn args_vars(&self) -> impl Iterator<Item = NamedVariable<'str, 'bump>> + '_ {
        self.args
            .iter()
            .zip(self.args_name.iter())
            .enumerate()
            .map(|(id, (sort, name))| NamedVariable {
                name: *name,
                variable: Variable { id, sort: *sort },
            })
    }

    /// all the [NamedVariable] that should be visible within a [ast::Step]
    pub fn args_vars_with_input(&self) -> impl Iterator<Item = NamedVariable<'str, 'bump>> + '_ {
        self.args_vars().chain([self.input_named_var()])
    }

    /// the special `in` variable
    pub fn input_named_var(&self) -> NamedVariable<'str, 'bump> {
        NamedVariable {
            name: "in",
            variable: Variable {
                id: self.args.len(),
                sort: MESSAGE.as_sort(),
            },
        }
    }

    pub fn substitution_input(&self) -> OneVarSubstF<'bump> {
        OneVarSubst {
            id: self.input_named_var().id(),
            f: INPUT.f_a(self.args_vars().map(|v| v.variable)),
        }
    }

    pub fn substitution(&self, args: &[ARichFormula<'bump>]) -> FrozenSubstF<'_, 'bump> {
        assert_eq!(args.len(), self.args.len());

        let vars = self.args_vars_with_input().map(|v| v.id()).collect();
        let formulas = args.iter().cloned().chain([INPUT.f_a(args)]).collect();

        FrozenSubst::new(vars, formulas)
    }
}

impl<'str, 'bump> NamedVariable<'str, 'bump> {
    pub fn variable(&self) -> Variable<'bump> {
        self.variable
    }

    pub fn name(&self) -> &'str str {
        self.name
    }

    pub fn sort(&self) -> Sort<'bump> {
        self.variable.sort
    }

    pub fn id(&self) -> usize {
        self.variable.id
    }
}

impl<'str, 'bump> Into<(&'str str, VarProxy<'bump>)> for NamedVariable<'str, 'bump> {
    fn into(self) -> (&'str str, VarProxy<'bump>) {
        let NamedVariable { name, variable } = self;
        (name, variable.into())
    }
}

impl<'str, 'bump> Into<Variable<'bump>> for NamedVariable<'str, 'bump> {
    fn into(self) -> Variable<'bump> {
        self.variable()
    }
}
