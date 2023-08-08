use if_chain::if_chain;
use itertools::Itertools;
use thiserror::Error;

use crate::formula::formula::ARichFormula;

use super::{
    super::{
        formula::{meq, RichFormula},
        sort::sorted::SortedError,
        variable::Variable,
    },
    substitution::variable_substitution::{
        OneVarSubst, OneVarSubstF, OwnedVarSubst, OwnedVarSubstF,
    },
    Substitution,
};

#[derive(Debug, Clone)]
pub struct Unifier<'bump> {
    /// variables on the left mapped to terms on the right
    left: OwnedVarSubst<ARichFormula<'bump>>,
    /// variables on the right mapped to terms on the left
    right: OwnedVarSubst<ARichFormula<'bump>>,
}

#[derive(Debug, Clone)]
pub struct OneWayUnifier<'bump> {
    subst: OwnedVarSubst<ARichFormula<'bump>>,
}

#[derive(Debug, Error)]
pub enum UnifierAsEqualityErr {
    #[error("found tow variables with the same id on both sides: {id:?}")]
    NonDisjointVariables { id: usize },
    #[error("sort is not defined in some of the formulas: {0:?}")]
    SortError(SortedError),
}

impl<'bump> Unifier<'bump> {
    /// Make a formula to check unifiability
    ///
    /// It returns an error if it can't deduce the sort of one of the variables or if a variables is used on the left *and* the right
    pub fn as_equalities(&'_ self) -> Result<Vec<ARichFormula<'bump>>, UnifierAsEqualityErr> {
        let left = &self.left.subst;
        let right = &self.right.subst;

        {
            // ensure there is no colisions of variables
            let (small, big) = ord_utils::sort_by(|a, b| a.len() < b.len(), left, right);

            let id_small = small.iter().map(OneVarSubst::id).collect_vec();
            if let Some(id) = big
                .iter()
                .map(OneVarSubst::id)
                .filter(|id| id_small.contains(&id))
                .next()
            {
                return Err(UnifierAsEqualityErr::NonDisjointVariables { id });
            }
        }

        // make the equalities
        let f = |ovs: &OneVarSubstF<'bump>| match ovs.f().get_sort() {
            Ok(sort) => Ok(meq(
                Variable::new(ovs.id(), sort).into_formula(),
                ovs.fc().clone(),
            )),
            Err(err) => Err(UnifierAsEqualityErr::SortError(err)),
        };

        left.iter().map(f).chain(right.iter().map(f)).collect()
    }

    /// the mgu of `x <-> f` where `x` is a formula
    pub fn one_variable_unifier(
        left_variable: &Variable<'bump>,
        right_formula: ARichFormula<'bump>,
    ) -> Self {
        let Variable { id, .. } = left_variable;
        Unifier {
            left: [(*id, right_formula)].into(),
            right: OwnedVarSubst::default(),
        }
    }

    pub fn does_unify(&self, left: &RichFormula<'bump>, right: &RichFormula<'bump>) -> bool {
        match (left, right) {
            (RichFormula::Fun(fun_l, args_l), RichFormula::Fun(fun_r, args_r))
                if fun_l == fun_r && args_l.len() == args_r.len() =>
            {
                args_l
                    .iter()
                    .zip(args_r.iter())
                    .all(|(l, r)| self.does_unify(l, r))
            }
            (RichFormula::Var(v), _) => {
                if let Some(left) = self.left.get(v.id) {
                    self.does_unify(left.as_ref(), right)
                } else if let RichFormula::Var(v2) = right {
                    if let Some(right) = self.right.get(v2.id) {
                        self.does_unify(left, right.as_ref())
                    } else {
                        v == v2
                    }
                } else {
                    false
                }
            }
            (_, RichFormula::Var(v)) => {
                if let Some(right) = self.right.get(v.id) {
                    self.does_unify(left, right.as_ref())
                } else if let RichFormula::Var(v2) = right {
                    if let Some(left) = self.left.get(v2.id) {
                        self.does_unify(left.as_ref(), right)
                    } else {
                        v == v2
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    pub fn mgu(left: &ARichFormula<'bump>, right: &ARichFormula<'bump>) -> Option<Self> {
        fn aux<'bump>(
            left: &ARichFormula<'bump>,
            right: &ARichFormula<'bump>,
            left_p: &mut OwnedVarSubstF<'bump>,
            right_p: &mut OwnedVarSubstF<'bump>,
        ) -> bool {
            match (left.as_ref(), right.as_ref()) {
                (RichFormula::Var(vl), RichFormula::Var(vr)) if vl == vr => true,
                (RichFormula::Var(v), _) => match left_p.get(v.id).cloned() {
                    Some(nl) if nl.is_var() => match (nl.as_ref(), right.as_ref()) {
                        (RichFormula::Var(v2), RichFormula::Var(v3)) => {
                            v2 == v3 || {
                                if let Some(r) = right_p.get_as_rf(v3.id) {
                                    nl.as_ref() == r
                                } else {
                                    right_p.add(v3.id, nl.shallow_copy());
                                    true
                                }
                            }
                        }
                        _ => false,
                    },
                    Some(nl) => aux(&nl, right, left_p, right_p),
                    None => {
                        left_p.add(v.id, right.shallow_copy());
                        true
                    }
                },
                (_, RichFormula::Var(v)) => match right_p.get(v.id).cloned() {
                    Some(nr) if nr.is_var() => match (nr.as_ref(), left.as_ref()) {
                        (RichFormula::Var(v2), RichFormula::Var(v3)) => {
                            v2 == v3 || {
                                if let Some(r) = left_p.get(v3.id) {
                                    &nr == r
                                } else {
                                    left_p.add(v3.id, nr.shallow_copy());
                                    true
                                }
                            }
                        }
                        _ => false,
                    },
                    Some(nl) => aux(&nl, right, left_p, right_p),
                    None => {
                        right_p.add(v.id, left.shallow_copy());
                        true
                    }
                },
                (RichFormula::Fun(fl, args_l), RichFormula::Fun(fr, args_r))
                    if fl == fr && args_l.len() == args_r.len() =>
                {
                    args_l
                        .iter()
                        .zip(args_r.iter())
                        .all(|(left, right)| aux(left, right, left_p, right_p))
                }
                _ => false,
            }
        }

        let mut left_p = OwnedVarSubst::new();
        let mut right_p = OwnedVarSubst::new();

        if aux(left, right, &mut left_p, &mut right_p) {
            Some(Unifier {
                left: left_p,
                right: right_p,
            })
        } else {
            None
        }
    }

    pub fn left(&self) -> &(impl Substitution<'bump>)
where {
        &self.left
    }

    pub fn right(&self) -> &(impl Substitution<'bump>)
where
        // 'bump: 'b
    {
        &self.right
    }

    pub fn is_unifying_to_variable(&self) -> Option<OneVarSubstF<'bump>> {
        if_chain! {
            if self.left.subst.is_empty();
            if self.right.subst.len() == 1;
            // if let Some(ovs) = self.right.field1.first();
            then {
                self.right.subst.first().cloned()
            } else {
                None
            }
        }
    }
}

impl<'bump> OneWayUnifier<'bump> {
    pub fn new(from: &ARichFormula<'bump>, to: &ARichFormula<'bump>) -> Option<Self> {
        fn aux<'a, 'bump>(
            from: &ARichFormula<'bump>,
            to: &ARichFormula<'bump>,
            p: &mut OwnedVarSubst<ARichFormula<'bump>>,
        ) -> bool {
            match (from.as_ref(), to.as_ref()) {
                (RichFormula::Var(v), _) => {
                    if let Some(nf) = p.get(v.id) {
                        nf == to
                    } else {
                        p.add(v.id, to.shallow_copy());
                        true
                    }
                }
                (RichFormula::Fun(funl, argsl), RichFormula::Fun(funr, argsr))
                    if funl == funr && argsl.len() == argsr.len() =>
                {
                    argsl.iter().zip(argsr.iter()).all(|(l, r)| aux(l, r, p))
                }
                _ => false,
            }
        }

        let mut p = OwnedVarSubst::new();

        if aux(from, to, &mut p) {
            Some(OneWayUnifier { subst: p })
        } else {
            None
        }
    }

    pub fn vars<'b: 'bump>(&'b self) -> impl Iterator<Item = usize> + 'b {
        self.subst.subst.iter().map(OneVarSubst::id)
    }
}
