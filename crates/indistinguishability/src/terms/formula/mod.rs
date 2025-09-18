use std::borrow::Cow;

use egg::Var;
use logic_formula::{Destructed, Formula};
use steel_derive::Steel;

use crate::terms::{Function, Sort, CONS, EXISTS, FIND_SUCH_THAT};

mod egg_like;
mod enum_like;
mod rec_exp_lang;

pub use egg_like::InnerLang;
pub use enum_like::RecFOFormula;
pub use rec_exp_lang::RecExprIter;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Steel)]
pub enum FOBinder {
    Forall,
    Exists,
    FindSuchThat,
}

pub struct RecFOFormulaQuant<'a> {
    pub quantifier: FOBinder,
    pub vars: Cow<'a, [Var]>,
    pub sorts: Cow<'a, [Sort]>,
}

impl<'a> RecFOFormulaQuant<'a> {
    pub fn new(quantifier: FOBinder, vars: Cow<'a, [Var]>, sorts: Cow<'a, [Sort]>) -> Self {
        Self {
            quantifier,
            vars,
            sorts,
        }
    }
}

impl FOBinder {
    pub fn try_from_function(fun:&Function) -> Option<Self> {
        match fun {
            _ if fun == &EXISTS => Some(Self::Exists),
            _ if fun == &FIND_SUCH_THAT => Some(Self::FindSuchThat),
            _ => None
        }
    }
}

impl<'a> logic_formula::Bounder<Var> for RecFOFormulaQuant<'a> {
    fn bounds(&self) -> impl Iterator<Item = Var> {
        self.vars.iter().copied()
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
}

mod sort_list {
    use itertools::Itertools;
    use logic_formula::{Destructed, Formula};

    use crate::terms::{CONS, Function, NIL, Sort};

    fn inner<F>(f: F, sorts: &mut Vec<Sort>) -> Option<()>
    where
        F: Formula<Fun = Function>,
    {
        let Destructed { head, args } = f.destruct();

        match head.as_fun() {
            Some(f) if f == &CONS => {
                let (hd, tl) = args.collect_tuple()?;
                let s = Sort::from_function(hd.destruct().head.as_fun()?)?;
                sorts.push(s);
                inner(tl, sorts)
            }
            Some(f) if f == &NIL => Some(()),
            _ => None,
        }
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
    pub fn try_get<F: Formula<Fun = Function>>(f: F) -> Option<Vec<Sort>> {
        let mut sorts = vec![];
        inner(f, &mut sorts)?;
        Some(sorts)
    }
}


pub trait FormulaLike  {
    type  F<'a> : Formula where Self: 'a;
    fn as_formula(&self) -> Self::F<'_>;

    fn destruct(&self) -> Destructed<Self::F<'_>, impl Iterator<Item = Self::F<'_>>> {
        self.as_formula().destruct()
    }
}