use if_chain::if_chain;
use itertools::Itertools;
use thiserror::Error;

use super::super::formula::{RichFormula, meq};
use super::super::sort::sorted::SortedError;
use super::super::variable::Variable;
use super::Substitution;
use super::substitution::variable_substitution::{
    MulitpleVarSubstF, MultipleVarSubst, OneVarSubst, OneVarSubstF,
};
use crate::formula::formula::ARichFormula;
use crate::formula::variable::uvar;

#[derive(Debug, Clone)]
pub struct Unifier<'bump> {
    /// variables on the left mapped to terms on the right
    left: MultipleVarSubst<ARichFormula<'bump>>,
    /// variables on the right mapped to terms on the left
    right: MultipleVarSubst<ARichFormula<'bump>>,
}

#[derive(Debug, Error)]
pub enum UnifierAsEqualityErr {
    #[error("found tow variables with the same id on both sides: {id:?}")]
    NonDisjointVariables { id: uvar },
    #[error("sort is not defined in some of the formulas: {0:?}")]
    SortError(SortedError),
}

impl<'bump> Unifier<'bump> {
    /// Make a formula to check unifiability
    ///
    /// It returns an error if it can't deduce the sort of one of the variables or if a variables is used on the left *and* the right
    pub fn as_equalities(&'_ self) -> Result<Vec<ARichFormula<'bump>>, UnifierAsEqualityErr> {
        let left = self.left.subst();
        let right = self.right.subst();

        {
            // ensure there is no colisions of variables
            let (small, big) = utils::ord_util::sort_by(|a, b| a.len() < b.len(), left, right);

            let id_small = small.iter().map(OneVarSubst::id).collect_vec();
            if let Some(id) = big
                .iter()
                .map(OneVarSubst::id)
                .find(|id| id_small.contains(id))
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
            right: MultipleVarSubst::default(),
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
                if let Some(left) = self.left.maybe_get(v.id) {
                    self.does_unify(left.as_ref(), right)
                } else if let RichFormula::Var(v2) = right {
                    if let Some(right) = self.right.maybe_get(v2.id) {
                        self.does_unify(left, right.as_ref())
                    } else {
                        v == v2
                    }
                } else {
                    false
                }
            }
            (_, RichFormula::Var(v)) => {
                if let Some(right) = self.right.maybe_get(v.id) {
                    self.does_unify(left, right.as_ref())
                } else if let RichFormula::Var(v2) = right {
                    if let Some(left) = self.left.maybe_get(v2.id) {
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
            left_p: &mut MulitpleVarSubstF<'bump>,
            right_p: &mut MulitpleVarSubstF<'bump>,
        ) -> bool {
            match (left.as_ref(), right.as_ref()) {
                (RichFormula::Var(vl), RichFormula::Var(vr)) if vl == vr => true,
                (RichFormula::Var(v), _) => match left_p.maybe_get(v.id).cloned() {
                    Some(nl) if nl.is_var() => match (nl.as_ref(), right.as_ref()) {
                        (RichFormula::Var(v2), RichFormula::Var(v3)) => {
                            v2 == v3 || {
                                if let Some(r) = right_p.maybe_get_as_rf(v3.id) {
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
                (_, RichFormula::Var(v)) => match right_p.maybe_get(v.id).cloned() {
                    Some(nr) if nr.is_var() => match (nr.as_ref(), left.as_ref()) {
                        (RichFormula::Var(v2), RichFormula::Var(v3)) => {
                            v2 == v3 || {
                                if let Some(r) = left_p.maybe_get(v3.id) {
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
                    itertools::zip_eq(args_l.iter(), args_r.iter())
                        .all(|(left, right)| aux(left, right, left_p, right_p))
                }
                _ => false,
            }
        }

        let mut left_p = MultipleVarSubst::new();
        let mut right_p = MultipleVarSubst::new();

        if aux(left, right, &mut left_p, &mut right_p) {
            Some(Unifier {
                left: left_p,
                right: right_p,
            })
        } else {
            None
        }
    }

    pub fn left(&self) -> &impl Substitution<'bump>
where {
        &self.left
    }

    pub fn right(&self) -> &impl Substitution<'bump>
where
        // 'bump: 'b
    {
        &self.right
    }

    /// if the right is just a variable, this return the substitution
    pub fn is_unifying_to_variable(&self) -> Option<OneVarSubstF<'bump>> {
        if_chain! {
            if self.left.subst().is_empty();
            if self.right.subst().len() == 1;
            // if let Some(ovs) = self.right.field1.first();
            then {
                self.right.subst().first().cloned()
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Unifier;
    use crate::container::ScopedContainer;
    use crate::formula::formula;
    use crate::formula::function::Function;
    use crate::formula::function::builtin::INPUT;
    use crate::formula::function::name_caster_collection::{
        DEFAULT_NAME_CASTER, NameCasterCollection,
    };
    use crate::formula::sort::Sort;
    use crate::formula::sort::builtins::{MESSAGE, NAME, STEP};
    use crate::formula::utils::Applicable;
    use crate::formula::variable::{Variable, uvar};
    fn vars<const N: usize>(mut i: uvar, sorts: [Sort<'_>; N]) -> [Variable<'_>; N] {
        sorts.map(|sort| {
            i += 1;
            Variable { id: i, sort }
        })
    }

    struct A<'bump> {
        hash: Function<'bump>,
        k0: Function<'bump>,
        k1: Function<'bump>,
        name_caster: NameCasterCollection<'bump>,
    }

    fn setup<F>(f: F)
    where
        F: for<'a> FnOnce(A<'a>),
    {
        let message = MESSAGE.as_sort();
        let step = STEP.as_sort();

        ScopedContainer::scoped(|container| {
            let hash =
                Function::new_user_term_algebra(container, "hash", [message; 2], message).main;
            let k0 =
                Function::new_user_term_algebra(container, "key", [step; 2], NAME.as_sort()).main;
            let k1 =
                Function::new_user_term_algebra(container, "key2", [step; 2], NAME.as_sort()).main;
            let name_caster = DEFAULT_NAME_CASTER.clone();

            let a = A {
                hash,
                k0,
                k1,
                name_caster,
            };
            f(a)
        })
    }

    #[test]
    fn mgu1() {
        let message = MESSAGE.as_sort();
        let step = STEP.as_sort();

        setup(
            |A {
                 hash,
                 k1,
                 name_caster,
                 ..
             }| {
                let [v1, v2, v3, v4, v5] = vars(0, [message, step, step, step, message]);

                let a = hash.f([v1.into(), name_caster.cast(message, k1.f([v2, v3]))]);
                println!("a = {a}");
                let b = hash.f([v5.into(), name_caster.cast(message, k1.f([v3, v4]))]);
                println!("b = {b}");

                let u = Unifier::mgu(&a, &b).unwrap();

                let u_str = formula::ands(u.as_equalities().unwrap());
                println!("{u_str}")
            },
        )
    }

    #[test]
    fn mgu2() {
        let message = MESSAGE.as_sort();
        let step = STEP.as_sort();

        setup(
            |A {
                 hash,
                 k1,
                 name_caster,
                 ..
             }| {
                let [v1, v2, v3, v4, _] = vars(0, [message, step, step, step, message]);

                let a = hash.f([v1.into(), name_caster.cast(message, k1.f([v2, v3]))]);
                println!("a = {a}");
                let b = hash.f([INPUT.f([v2]), name_caster.cast(message, k1.f([v3, v4]))]);
                println!("b = {b}");

                let u = Unifier::mgu(&a, &b).unwrap();

                let u_str = formula::ands(u.as_equalities().unwrap());
                println!("{u_str}")
            },
        )
    }

    #[test]
    fn mgu_fail() {
        let message = MESSAGE.as_sort();
        let step = STEP.as_sort();

        setup(
            |A {
                 hash,
                 k1,
                 k0,
                 name_caster,
                 ..
             }| {
                let [v1, v2, v3, v4, v5] = vars(0, [message, step, step, step, message]);

                let a = hash.f([v1.into(), name_caster.cast(message, k1.f([v2, v3]))]);
                println!("a = {a}");
                let b = hash.f([v5.into(), name_caster.cast(message, k0.f([v3, v4]))]);
                println!("b = {b}");

                let u = Unifier::mgu(&a, &b);
                assert!(u.is_none())
            },
        )
    }
}
