use super::FunctionCollection;
use crate::{
    Lang,
    terms::{Function, Sort},
};
use egg::{PatternAst, Var};
use itertools::{Itertools, chain};
use logic_formula::Formula;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Exists {
    /// The free variables captured by the quantifier
    pub vars: Vec<Var>,
    /// The variable bound by the quantifier
    pub bound_var: Var,
    /// The "content" of the quantifier
    pub patt: PatternAst<Lang>,
    /// the main alias (e.g., `exists$1`)
    ///
    /// stands for "top level function"
    pub tlf: Function,
    /// the skolem function
    pub skolem: Function,
    /// the fresh constant replacing the index
    pub fresh: Function,
}

impl Exists {
    pub fn is_uninit(&self) -> bool {
        self.patt.is_empty()
    }

    pub fn valid(&self, idx: usize, funs: &FunctionCollection) -> bool {
        let Self {
            vars,
            bound_var,
            patt,
            tlf,
            skolem,
            fresh,
        } = self;
        let all_vars = chain!(vars, [bound_var]).copied().collect_vec();

        (
            // is at idx
            funs.quantifiers().get(idx) == Some(self)
        ) && ({
            // mapping between variables
            let vars: Vec<_> = patt.free_vars_iter().collect();
            crate::utils::same_slice(&all_vars, &vars)
        }) && (
            // reciprocal
            tlf.get_exist_index() == Some(idx)
                && skolem.get_exist_index() == Some(idx)
                && fresh.get_exist_index() == Some(idx)
        ) && (
            // arities
            tlf.arity() == all_vars.len() && skolem.arity() == vars.len() && fresh.arity() == 0
        )
    }

    pub fn get_var_sort(&self) -> Sort {
        self.fresh.signature.output
    }

    pub fn get_functions(&self) -> [&Function; 3] {
        let Self {
            tlf, skolem, fresh, ..
        } = self;
        [tlf, skolem, fresh]
    }
}

#[derive(Debug)]
pub struct ExistsFuns {
    pub tlf: Function,
    pub skolem: Function,
    pub fresh: Function,
}

#[derive(Debug)]
pub struct ExistsBuilder {
    /// The free variables captured by the quantifier
    pub vars: Vec<Var>,
    /// The variable bound by the quantifier
    pub bound_var: Var,
    /// The "content" of the quantifier
    pub patt: PatternAst<Lang>,
}
