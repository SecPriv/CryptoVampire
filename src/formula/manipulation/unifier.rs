use itertools::Itertools;
use thiserror::Error;
use if_chain::if_chain;

use super::{super::{
    formula::{meq, RichFormula},
    sort::sorted::SortedError,
    variable::Variable,
}, Substitution, OwnedVarSubst};

#[derive(Debug, Clone)]
pub struct Unifier<'a, 'bump>
where
    'bump: 'a,
{
    /// variables on the left mapped to terms on the right
    left: OwnedVarSubst<&'a RichFormula<'bump>>,
    /// variables on the right mapped to terms on the left
    right: OwnedVarSubst<&'a RichFormula<'bump>>,
}

#[derive(Debug, Clone)]
pub struct OneWayUnifier<'a, 'bump> {
    subst: OwnedVarSubst<&'a RichFormula<'bump>>,
}

#[derive(Debug, Error)]
pub enum UnifierAsEqualityErr {
    #[error("found tow variables with the same id on both sides: {id:?}")]
    NonDisjointVariables { id: usize },
    #[error("sort is not defined in some of the formulas: {0:?}")]
    SortError(SortedError),
}

impl<'a, 'bump> Unifier<'a, 'bump>
where
    'bump: 'a,
{
    /// Make a formula to check unifiability
    ///
    /// It returns an error if it can't deduce the sort of one of the variables or if a variables is used on the left *and* the right
    pub fn as_equalities(&'_ self) -> Result<Vec<RichFormula<'bump>>, UnifierAsEqualityErr> {
        let left = &self.left.field1;
        let right = &self.right.field1;

        {
            // ensure there is no colisions of variables
            let (small, big) = ord_utils::sort_by(|a, b| a.len() < b.len(), left, right);

            let id_small = small.iter().map(|(id, _)| *id).collect_vec();
            if let Some(id) = big
                .iter()
                .map(|(id, _)| *id)
                .filter(|id| id_small.contains(&id))
                .next()
            {
                return Err(UnifierAsEqualityErr::NonDisjointVariables { id });
            }
        }

        // make the equalities
        let f = |(id, formula): &(usize, &'a RichFormula<'bump>)| match formula.get_sort() {
            Ok(sort) => Ok(meq(
                Variable::new(*id, sort).into_formula(),
                (*formula).clone(),
            )),
            Err(err) => Err(UnifierAsEqualityErr::SortError(err)),
        };

        left.iter().map(f).chain(right.iter().map(f)).collect()
    }

    /// the mgu of `x <-> f` where `x` is a formula
    pub fn one_variable_unifier(
        left_variable: &Variable<'bump>,
        right_formula: &'a RichFormula<'bump>,
    ) -> Self {
        let Variable { id, .. } = left_variable;
        Unifier {
            left: OwnedVarSubst { field1: vec![(*id, right_formula)] },
            right: OwnedVarSubst { field1: vec![] } ,
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
                if let Some(&left) = self.left.get(v.id) {
                    self.does_unify(left, right)
                } else if let RichFormula::Var(v2) = right {
                    if let Some(&right) = self.right.get(v2.id) {
                        self.does_unify(left, right)
                    } else {
                        v == v2
                    }
                } else {
                    false
                }
            }
            (_, RichFormula::Var(v)) => {
                if let Some(&right) = self.right.get(v.id) {
                    self.does_unify(left, right)
                } else if let RichFormula::Var(v2) = right {
                    if let Some(&left) = self.left.get(v2.id) {
                        self.does_unify(left, right)
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

    pub fn mgu(left: &'a RichFormula<'bump>, right: &'a RichFormula<'bump>) -> Option<Self> {
        fn aux<'a, 'bump>(
            left: &'a RichFormula<'bump>,
            right: &'a RichFormula<'bump>,
            left_p: &mut OwnedVarSubst<&'a RichFormula<'bump>>,
            right_p: &mut OwnedVarSubst<&'a RichFormula<'bump>>,
        ) -> bool {
            match (left, right) {
                (RichFormula::Var(vl), RichFormula::Var(vr)) if vl == vr => true,
                (RichFormula::Var(v), _) => match left_p.get(v.id) {
                    Some(nl @ RichFormula::Var(v2)) => match right {
                        RichFormula::Var(v3) => {
                            v2 == v3 || {
                                if let Some(&r) = right_p.get(v3.id) {
                                    nl == &r
                                } else {
                                    right_p.add(v3.id, nl);
                                    true
                                }
                            }
                        }
                        _ => false,
                    },
                    Some(nl) => aux(nl, right, left_p, right_p),
                    None => {
                        left_p.add(v.id, right);
                        true
                    }
                },
                (_, RichFormula::Var(v)) => match right_p.get(v.id) {
                    Some(nr @ RichFormula::Var(v2)) => match left {
                        RichFormula::Var(v3) => {
                            v2 == v3 || {
                                if let Some(&r) = left_p.get(v3.id) {
                                    nr == &r
                                } else {
                                    left_p.add(v3.id, nr);
                                    true
                                }
                            }
                        }
                        _ => false,
                    },
                    Some(nl) => aux(nl, right, left_p, right_p),
                    None => {
                        right_p.add(v.id, left);
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

    pub fn left(&self) -> &(impl Substitution<'bump> + 'a)
where {
        &self.left
    }

    pub fn right(&self) -> &(impl Substitution<'bump> + 'a)
where
        // 'bump: 'b
    {
        &self.right
    }

    pub fn is_unifying_to_variable(&self) -> Option<(usize, &RichFormula<'bump>)> {
        if_chain! {
            if self.left.field1.is_empty();
            if self.right.field1.len() == 1;
            if let Some((id, t)) = self.right.field1.first();
            then {
                Some((*id, t))
            } else {
                None
            }
        }
    }
}

impl<'a, 'bump> OneWayUnifier<'a, 'bump>
where
    'bump: 'a,
{
    pub fn new(from: &'a RichFormula<'bump>, to: &'a RichFormula<'bump>) -> Option<Self> {
        fn aux<'a, 'bump>(
            from: &'a RichFormula<'bump>,
            to: &'a RichFormula<'bump>,
            p: &mut OwnedVarSubst<&'a RichFormula<'bump>>,
        ) -> bool {
            match (from, to) {
                (RichFormula::Var(v), _) => {
                    if let Some(&nf) = p.get(v.id) {
                        nf == to
                    } else {
                        p.add(v.id, to);
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
        self.subst.field1.iter().map(|(i, _)| *i)
    }
}