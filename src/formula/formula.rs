use std::collections::HashSet;
use std::fmt;
use std::ops::Deref;

use crate::problem::problem::Problem;

use super::{
    env::Environement,
    function::Function,
    quantifier::Quantifier,
    sort::Sort,
    unifier::{Substitution, Translate},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RichFormula {
    Var(Variable),
    Fun(Function, Vec<RichFormula>),
    Quantifier(Quantifier, Vec<RichFormula>),
}

#[derive(Debug, PartialOrd, Ord, Hash, Clone)]
pub struct Variable {
    pub id: usize,
    pub sort: Sort,
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "X{}", self.id)
    }
}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        if cfg!(debug_assertions) {
            if self.id == other.id {
                assert_eq!(self.sort, other.sort);
                true
            } else {
                false
            }
        } else {
            self.id == other.id
        }
    }
}

impl Eq for Variable {}

impl RichFormula {
    pub fn get_sort<'a>(&self, env: &Environement) -> Sort {
        match self {
            RichFormula::Var(v) => v.sort.clone(),
            RichFormula::Fun(f, _) => f.get_output_sort(),
            RichFormula::Quantifier(q, _) => q.get_output_sort(env).clone(),
        }
    }

    pub fn get_free_vars(&self) -> Vec<&Variable> {
        let mut free_vars = Vec::new();
        let mut bound_vars = Vec::new();
        // let mut bounded = Vec::new();

        // fn aux<'a>(bounded: &mut Vec<&'a Variable>, r: &mut Vec<&'a Variable>, t: &'a RichFormula) {
        //     match t {
        //         RichFormula::Fun(_, args) => args.iter().for_each(|f| aux(bounded, r, f)),
        //         RichFormula::Var(v) if !bounded.contains(&v) => {
        //             dbg!(&v);
        //             dbg!(&bounded);
        //             r.push(v)},
        //         RichFormula::Quantifier(q, args) => {
        //             let vars = q.get_variables();
        //             let n = vars.len();
        //             debug_assert!(!vars.iter().any(|v| bounded.contains(&v)));
        //             bounded.extend(vars.into_iter());
        //             args.iter().for_each(|f| aux(bounded, r, f));
        //             bounded.truncate(bounded.len() - n);
        //         }
        //         _ => {}
        //     }
        // }
        // aux(&mut bounded, &mut r, self);
        // r

        for f in self.iter() {
            match f {
                RichFormula::Var(v) if !(free_vars.contains(&v) || bound_vars.contains(&v)) => {
                    free_vars.push(v)
                }
                RichFormula::Quantifier(q, _) => {
                    for v in q.get_variables() {
                        debug_assert!(
                            !free_vars.contains(&v),
                            "\n\tfv:{:?}\n\t{:?}",
                            &free_vars,
                            &v
                        );
                        if !bound_vars.contains(&v) {
                            bound_vars.push(v)
                        }
                    }
                }
                _ => {}
            }
        }
        free_vars
    }

    pub fn get_used_variables(&'_ self) -> HashSet<&'_ Variable> {
        fn aux<'a>(data: &mut HashSet<&'a Variable>, f: &'a RichFormula) {
            match f {
                RichFormula::Var(v) => {
                    data.insert(v);
                }
                RichFormula::Fun(_, args) => args.iter().for_each(|f| aux(data, f)),
                RichFormula::Quantifier(q, args) => {
                    data.extend(q.get_variables().iter().map(|v| v));
                    args.iter().for_each(|f| aux(data, f))
                }
            }
        }

        let mut data = HashSet::new();
        aux(&mut data, self);
        data
    }

    // pub fn apply(self, var: &Variable, f: &Self) -> Self {
    //     match self {
    //         RichFormula::Var(v) if &v == var => f.clone(),
    //         RichFormula::Fun(fun, args) => RichFormula::Fun(
    //             fun,
    //             args.into_iter().map(|old_f| old_f.apply(var, f)).collect(),
    //         ),
    //         RichFormula::Quantifier(q, args) => RichFormula::Quantifier(
    //             q,
    //             args.into_iter().map(|old_f| old_f.apply(var, f)).collect(),
    //         ),
    //         _ => self,
    //     }
    // }

    pub fn iter(&self) -> impl Iterator<Item = &RichFormula> {
        let mut pile = vec![self];
        std::iter::from_fn(move || {
            if let Some(f) = pile.pop() {
                match f {
                    RichFormula::Var(_) => {}
                    RichFormula::Fun(_, args) => pile.extend(args.iter()),
                    RichFormula::Quantifier(_, args) => pile.extend(args.iter()),
                }
                Some(f)
            } else {
                None
            }
        })
    }

    pub fn iter_with_quantifier<'a>(
        &'a self,
        pbl: &'a Problem,
    ) -> impl Iterator<Item = &'a RichFormula> {
        let mut pile = vec![self];
        std::iter::from_fn(move || {
            if let Some(f) = pile.pop() {
                match f {
                    RichFormula::Var(_) => {}
                    RichFormula::Fun(fun, _) if fun.is_from_quantifer() => {
                        let q = pbl.quantifiers.iter().find(|q| &q.function == fun).unwrap();
                        pile.extend(q.iter_content())
                    }
                    RichFormula::Fun(_, args) => pile.extend(args.iter()),
                    RichFormula::Quantifier(_, args) => pile.extend(args.iter()),
                }
                Some(f)
            } else {
                None
            }
        })
    }

    pub fn custom_iter_w_quantifier<'a, F, T>(
        &'a self,
        pbl: &'a Problem,
        f: F,
    ) -> impl Iterator<Item = T> + 'a
    where
        F: FnMut(&'a RichFormula, &'a Problem) -> (Option<T>, Vec<&'a RichFormula>) + 'a,
        T: 'a,
    {
        struct Iter<'a, F, T>
        where
            F: FnMut(&'a RichFormula, &'a Problem) -> (Option<T>, Vec<&'a RichFormula>),
        {
            pile: Vec<&'a RichFormula>,
            pbl: &'a Problem,
            f: F,
        }
        impl<'a, F, T> Iterator for Iter<'a, F, T>
        where
            F: FnMut(&'a RichFormula, &'a Problem) -> (Option<T>, Vec<&'a RichFormula>),
        {
            type Item = T;

            fn next(&mut self) -> Option<T> {
                match self.pile.pop() {
                    None => None,
                    Some(formula) => {
                        match formula {
                            RichFormula::Fun(fun, _) if fun.is_from_quantifer() => {
                                let q = self
                                    .pbl
                                    .quantifiers
                                    .iter()
                                    .find(|q| &q.function == fun)
                                    .unwrap();
                                self.pile.extend(q.iter_content())
                            }
                            RichFormula::Quantifier(_, args) => {
                                self.pile.extend(args.iter())
                            }
                            _ => {}
                        }
                        let (res, nexts) = (self.f)(formula, self.pbl);
                        self.pile.extend(nexts.into_iter());
                        if let Some(_) = res {
                            res
                        } else {
                            self.next()
                        }
                    }
                }
            }
        }

        Iter {
            f,
            pbl,
            pile: vec![self],
        }
    }

    pub fn map<F>(self, f: &F) -> Self
    where
        F: Fn(Self) -> Self,
    {
        match self {
            RichFormula::Var(_) => f(self),
            RichFormula::Fun(fun, args) => {
                f(Self::Fun(fun, args.into_iter().map(|x| x.map(f)).collect()))
            }
            RichFormula::Quantifier(q, args) => f(Self::Quantifier(
                q,
                args.into_iter().map(|x| x.map(f)).collect(),
            )),
        }
    }

    pub fn apply<F>(self, f: F) -> Self
    where
        F: Fn(&Variable) -> Self,
    {
        self.map(&{
            |form| match form {
                Self::Var(v) => f(&v),
                _ => form,
            }
        })
    }

    pub fn apply_some<F>(self, f: F) -> Self
    where
        F: Fn(&Variable) -> Option<Self>,
    {
        self.apply(|v| f(v).unwrap_or(Self::Var(v.clone())))
    }

    pub fn apply_substitution(self, vars: &[usize], fs: &[Self]) -> Self {
        debug_assert_eq!(vars.len(), fs.len());
        self.apply_some(|v| {
            vars.iter()
                .position(|v2| v2 == &v.id)
                .map(|i| fs[i].clone())
        })
    }

    pub fn apply_permutation2(&self, per: &impl Substitution) -> Self {
        per.apply(self)
    }

    pub fn translate_vars(&self, i: usize) -> Self {
        self.apply_permutation2(&Translate::new(i))
    }
}

impl Variable {
    pub fn new(id: usize, sort: Sort) -> Self {
        Self { id, sort }
    }
}

pub fn sorts_to_variables<I: Deref<Target = Sort>>(
    from: usize,
    s: impl Iterator<Item = I>,
) -> Vec<Variable> {
    s.enumerate()
        .map(|(i, s)| Variable::new(i + from, s.clone()))
        .collect()
}

impl From<Variable> for RichFormula {
    fn from(v: Variable) -> Self {
        RichFormula::Var(v)
    }
}
impl From<&Variable> for RichFormula {
    fn from(v: &Variable) -> Self {
        v.clone().into()
    }
}
