use std::fmt::Display;

use logic_formula::{Destructed, Formula};
use serde::Serialize;
use steel_derive::Steel;

use crate::terms::{EXISTS, FIND_SUCH_THAT, Function, Variable};

mod egg;
// mod egg_like;
mod enum_like;
// mod rec_exp_lang;
mod sexpr;

pub use egg::InnerLang;
pub(crate) use enum_like::QuantifierTranslator;
pub use enum_like::{RecFOFormula, substitution_utils};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Steel, Serialize)]
pub enum FOBinder {
    Forall,
    Exists,
    FindSuchThat,
}

pub struct RecFOFormulaQuant {
    pub quantifier: FOBinder,
    pub vars: Vec<Variable>,
}

pub struct RecFOFormulaQuantRef<'a> {
    pub quantifier: FOBinder,
    pub vars: &'a [Variable],
}

impl<'a> RecFOFormulaQuantRef<'a> {
    pub fn new(quantifier: FOBinder, vars: &'a [Variable]) -> Self {
        Self { quantifier, vars }
    }
}

impl RecFOFormulaQuant {
    pub fn new(quantifier: FOBinder, vars: Vec<Variable>) -> Self {
        Self { quantifier, vars }
    }
}

impl FOBinder {
    pub fn try_from_function(fun: &Function) -> Option<Self> {
        fun.as_fobinder()
    }

    pub fn arity(&self) -> usize {
        match self {
            Self::FindSuchThat => 3,
            Self::Exists | Self::Forall => 1,
        }
    }
}

impl logic_formula::Bounder<Variable> for RecFOFormulaQuant {
    fn bounds(&self) -> impl Iterator<Item = Variable> {
        self.vars.iter().cloned()
    }
}

impl<'a> logic_formula::Bounder<&'a Variable> for RecFOFormulaQuantRef<'a> {
    fn bounds(&self) -> impl Iterator<Item = &'a Variable> {
        self.vars.iter()
    }
}

impl FOBinder {
    /// The value taken by the quantifier on an empty set
    ///
    /// ```text
    /// \exists => false
    /// \forall => true
    /// ```
    pub fn on_empty(&self) -> bool {
        match self {
            FOBinder::Forall => true,
            FOBinder::Exists => false,
            _ => todo!(),
        }
    }

    pub fn as_function(&self) -> Option<&'static Function> {
        match self {
            FOBinder::Exists => Some(&EXISTS),
            FOBinder::FindSuchThat => Some(&FIND_SUCH_THAT),
            FOBinder::Forall => None,
        }
    }
}

impl Display for FOBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FOBinder::Forall => write!(f, "forall"),
            FOBinder::Exists => write!(f, "exists"),
            FOBinder::FindSuchThat => write!(f, "find_such_that"),
        }
    }
}

pub(crate) mod list {
    use egg::{Analysis, EGraph, Id};
    use itertools::Itertools;
    use logic_formula::{Destructed, Formula};
    use utils::econtinue_let;

    use crate::Lang;
    use crate::terms::{CONS, Function, LAMBDA_O, LAMBDA_S, NIL, Sort};

    fn inner<F>(f: F, sorts: &mut Vec<Sort>) -> Option<()>
    where
        F: Formula,
        F::Fun: AsRef<Function>,
    {
        let Destructed { head, args } = f.destruct();

        match head.as_fun() {
            Some(f) if f.as_ref() == &CONS => {
                let (hd, tl) = args.collect_tuple()?;
                let s = Sort::from_function(hd.destruct().head.as_fun()?.as_ref())?;
                sorts.push(s);
                inner(tl, sorts)
            }
            Some(f) if f.as_ref() == &NIL => Some(()),
            _ => None,
        }
    }

    pub fn snoc_egraph<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        f: Id,
    ) -> Result<Option<(Sort, Id)>, Id> {
        match egraph[f]
            .nodes
            .iter()
            .find(|f| f.head == NIL || f.head == CONS)
            .ok_or(f)?
        {
            Lang { head, .. } if head == &NIL => Ok(None),
            Lang { head, args } if head == &CONS => {
                let (&s, &rec) = args.iter().collect_tuple().ok_or(f)?;
                for h in egraph[s].nodes.iter().map(|x| &x.head) {
                    econtinue_let!(let Some(s) = Sort::from_function(h));
                    return Ok(Some((s, rec)));
                }
                Err(f)
            }
            _ => unreachable!(),
        }
    }

    fn inner_egraph<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        mut f: Id,
        sorts: &mut Vec<Sort>,
    ) -> Option<()> {
        while let Some((s, tl)) = snoc_egraph(egraph, f).ok()? {
            sorts.push(s);
            f = tl
        }
        Some(())
    }

    /// Attempts to extract a list of sorts from a formula.
    ///
    /// This function walks through a formula that is expected to be a list
    /// constructed using [CONS] and [NIL]. For each element in the list,
    /// it attempts to extract the sort of the head of that element.
    ///
    /// # Arguments
    ///
    /// * `f` - A formula representing a list, where elements are constructed
    ///   with `CONS` and terminated by `NIL`.
    ///
    /// # Returns
    ///
    /// * `Some(Vec<Sort>)` - A vector of sorts extracted from the list.
    /// * `None` - If the input formula does not match the expected structure
    ///   (e.g., it's not a proper list or an element has no associated sort).
    pub fn try_get<F>(f: F) -> Option<Vec<Sort>>
    where
        F: Formula,
        F::Fun: AsRef<Function>,
    {
        let mut sorts = vec![];
        inner(f, &mut sorts)?;
        Some(sorts)
    }

    /// Same as [try_get] but from an egraph
    pub fn try_get_egraph<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, f: Id) -> Option<Vec<Sort>> {
        let mut sorts = vec![];
        inner_egraph(egraph, f, &mut sorts)?;
        Some(sorts)
    }

    pub fn count_s<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, f: Id) -> Option<u32> {
        for n in egraph[f].iter() {
            if n.head == LAMBDA_O {
                return Some(0);
            } else if n.head == LAMBDA_S {
                return count_s(egraph, n.args[0]);
            }
        }
        None
    }
}

pub trait FormulaLike {
    type F<'a>: Formula
    where
        Self: 'a;
    fn as_formula(&self) -> Self::F<'_>;

    fn destruct(&self) -> Destructed<Self::F<'_>, impl Iterator<Item = Self::F<'_>>> {
        self.as_formula().destruct()
    }
}
