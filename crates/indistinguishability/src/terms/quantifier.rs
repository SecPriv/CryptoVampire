use egg::{PatternAst, Var};
use itertools::{chain, Itertools};
use logic_formula::Formula;
use serde::{Deserialize, Serialize};

use crate::Lang;

use super::FunctionCollection;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Quantifier {
    /// The kind of quantifier
    ///
    /// `find_such_that` are not handeled currently
    pub kind: QuantifierKind,
    /// The free variables captured by the quantifier
    pub vars: Vec<Var>,
    /// The variable bound by the quantifier
    pub bound_var: Var,
    /// The "content" of the quantifier
    pub patt: PatternAst<Lang>,
    /// index in the [FunctionCollection] for the main alias (e.g., `exists$1`)
    ///
    /// stands for "top level function"
    pub tlf: usize,
    /// index in the [FunctionCollection] for the skolem function
    pub skolem: usize,
    /// index in the [FunctionCollection] for the fresh constant replacing the index
    pub fresh: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum QuantifierKind {
    Exists,
    Forall,
}

impl Quantifier {
    pub fn valid(&self, idx: usize, funs: &FunctionCollection) -> bool {
        let Self {
            kind: _,
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
            // indices in range
            *tlf < funs.len() && *skolem < funs.len() && *fresh < funs.len()
        ) && (
            // reciprocal
            funs[*tlf].get_exist_index() == Some(idx)
                && funs[*skolem].get_exist_index() == Some(idx)
                && funs[*fresh].get_exist_index() == Some(idx)
        ) && (
            // arities
            funs[*tlf].arity() == all_vars.len()
                && funs[*skolem].arity() == vars.len()
                && funs[*fresh].arity() == 0
        )
    }

    pub(crate) fn points_to(&self) -> [usize; 3] {
      [self.tlf, self.skolem, self.fresh]
    }
}
