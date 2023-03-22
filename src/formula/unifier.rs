use super::{formula::RichFormula, variable::Variable};

#[derive(Debug, Clone)]
pub struct Unifier<'a, 'bump>
where
    'a: 'bump,
{
    left: ISubstitution<&'a RichFormula<'bump>>,
    right: ISubstitution<&'a RichFormula<'bump>>,
}

#[derive(Debug, Clone)]
pub struct OneWayUnifier<'a, 'bump> {
    subst: ISubstitution<&'a RichFormula<'bump>>,
}

#[derive(Debug, Clone)]
struct ISubstitution<T>(Vec<(usize, T)>);

impl<'bump, T> ISubstitution<T> {
    fn get(&self, id: usize) -> Option<&T> {
        self.0.iter().find(|(i, _)| i == &id).map(|(_, f)| f)
    }

    fn new() -> Self {
        Self(Vec::new())
    }
}

impl<'bump, 'a> ISubstitution<&'a RichFormula<'bump>> {
    fn add(&mut self, id: usize, r: &'a RichFormula<'bump>) {
        debug_assert!(self.0.iter().all(|(i, _)| i != &id));
        debug_assert!(match r {
            RichFormula::Var(v) => v.id != id,
            _ => true,
        });
        self.0.push((id, r))
    }
}

impl<'a, 'bump> Unifier<'a, 'bump>
where
    'a: 'bump,
{
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
            left_p: &mut ISubstitution<&'a RichFormula<'bump>>,
            right_p: &mut ISubstitution<&'a RichFormula<'bump>>,
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

        let mut left_p = ISubstitution::new();
        let mut right_p = ISubstitution::new();

        if aux(left, right, &mut left_p, &mut right_p) {
            Some(Unifier {
                left: left_p,
                right: right_p,
            })
        } else {
            None
        }
    }

    pub fn left<'b>(&'b self) -> &'b (impl Substitution + 'a)
    where
        'b: 'a,
    {
        &self.left
    }

    pub fn right<'b>(&'b self) -> &'b (impl Substitution + 'a)
    where
        'b: 'a,
    {
        &self.right
    }
}

impl<'a, 'bump> OneWayUnifier<'a, 'bump>
where
    'a: 'bump,
{
    pub fn new(from: &'a RichFormula<'bump>, to: &'a RichFormula<'bump>) -> Option<Self> {
        fn aux<'a, 'bump>(
            from: &'a RichFormula<'bump>,
            to: &'a RichFormula<'bump>,
            p: &mut ISubstitution<&'a RichFormula<'bump>>,
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

        let mut p = ISubstitution::new();

        if aux(from, to, &mut p) {
            Some(OneWayUnifier { subst: p })
        } else {
            None
        }
    }

    pub fn vars<'b: 'bump>(&'b self) -> impl Iterator<Item = usize> + 'b {
        self.subst.0.iter().map(|(i, _)| *i)
    }
}

pub trait Substitution<'bump> {
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump>;

    fn apply(&self, f: &RichFormula<'bump>) -> RichFormula<'bump> {
        match f {
            RichFormula::Var(v) => self.get(v),
            RichFormula::Fun(fun, args) => RichFormula::Fun(
                fun.clone(),
                args.iter().map(|arg| self.apply(arg)).collect(),
            ),
            RichFormula::Quantifier(q, args) => {
                RichFormula::Quantifier(q.clone(), args.iter().map(|arg| self.apply(arg)).collect())
            }
        }
    }

    fn chain<O>(self: Self, other: O) -> Chain<Self, O>
    where
        Self: Sized,
        O: Substitution<'bump> + Sized,
    {
        Chain(self, other)
    }

    fn translate(self, i: usize) -> Chain<Self, Translate>
    where
        Self: Sized,
    {
        self.chain(Translate(i))
    }
}

impl<'a, 'bump> Substitution<'bump> for ISubstitution<&'a RichFormula<'bump>>
where
    'a: 'bump,
{
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        self.0
            .iter()
            .find(|(nid, _)| nid == &var.id)
            .map(|(_, f)| RichFormula::clone(f))
            .unwrap_or(RichFormula::Var(var.clone()))
    }
}

pub struct Chain<A, B>(A, B);

impl<'bump, A: Substitution<'bump>, B: Substitution<'bump>> Substitution<'bump> for Chain<A, B> {
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        self.0.get(var).apply_permutation2(&self.1)
    }
}

pub struct Translate(usize);

impl Translate {
    pub fn new(i: usize) -> Self {
        Translate(i)
    }
}

impl<'bump> Substitution<'bump> for Translate {
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        RichFormula::Var(Variable {
            id: var.id + self.0,
            ..var.clone()
        })
    }
}
