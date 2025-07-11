use std::fmt::Display;

use egg::{PatternAst, Var};
use itertools::{Itertools, chain};
use logic_formula::Formula;

use super::FunctionCollection;
use crate::Lang;
use crate::terms::{Function, Sort};

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

        let is_at_idx = {
            // is at idx
            funs.quantifiers().get(idx) == Some(self)
        };
        let map_vars = {
            // mapping between variables
            let vars: Vec<_> = patt.free_vars_iter().collect();
            crate::utils::same_slice(&all_vars, &vars)
        };
        let reciprocal = {
            // reciprocal
            tlf.get_exist_index() == Some(idx)
                && skolem.get_exist_index() == Some(idx)
                && fresh.get_exist_index() == Some(idx)
        };
        let arities = {
            // arities
            tlf.arity() == all_vars.len() && skolem.arity() == vars.len() && fresh.arity() == 0
        };
        debug_assert!(is_at_idx);
        debug_assert!(map_vars);
        debug_assert!(reciprocal);
        debug_assert!(arities);
        is_at_idx && map_vars && reciprocal && arities
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

impl Display for Exists {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Exists {
            vars,
            bound_var,
            patt,
            tlf,
            skolem,
            fresh,
        } = self;

        write!(f, "∃{tlf}(")?;
        for v in vars {
            write!(f, "{v}, ")?;
        }
        write!(f, ") {bound_var}@({fresh}, {skolem}). {patt}")
    }
}
