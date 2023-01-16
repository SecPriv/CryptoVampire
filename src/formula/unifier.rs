use super::formula::RichFormula;

#[derive(Debug, Clone)]
pub struct Unifier<'a> {
    left: Permutation<&'a RichFormula>,
    right: Permutation<&'a RichFormula>,
}

#[derive(Debug, Clone)]
struct Permutation<T>(Vec<(usize, T)>);

impl<T> Permutation<T> {
    fn get(&self, id: usize) -> Option<&T> {
        self.0.iter().find(|(i, _)| i == &id).map(|(_, f)| f)
    }

    fn new() -> Self {
        Self(Vec::new())
    }
}

impl<'a> Permutation<&'a RichFormula> {
    fn add(&mut self, id: usize, r: &'a RichFormula) {
        debug_assert!(self.0.iter().all(|(i, _)| i != &id));
        debug_assert!(match r {
            RichFormula::Var(v) => v.id != id,
            _ => true,
        });
        self.0.push((id, r))
    }
}

impl<'a> Unifier<'a> {
    pub fn does_unify(&self, left: &RichFormula, right: &RichFormula) -> bool {
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

    pub fn mgu(left: &'a RichFormula, right: &'a RichFormula) -> Option<Self> {
        fn aux<'a>(
            left: &'a RichFormula,
            right: &'a RichFormula,
            left_p: &mut Permutation<&'a RichFormula>,
            right_p: &mut Permutation<&'a RichFormula>,
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
                        _ => false
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
                        _ => false
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

        let mut left_p = Permutation::new();
        let mut right_p = Permutation::new();

        if aux(left, right, &mut left_p, &mut right_p) {
            Some(Unifier {
                left: left_p,
                right: right_p,
            })
        } else {
            None
        }
    }
}
