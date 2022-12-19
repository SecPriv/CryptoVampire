use std::fmt;

use super::{function::Function, quantifier::Quantifier, sort::Sort};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RichFormula {
    Var(Variable),
    Fun(Function, Vec<RichFormula>),
    Quantifier(Quantifier, Vec<RichFormula>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Formula {
    Var(Variable),
    Fun(Function, Vec<Formula>),
    Forall(Vec<Variable>, Box<Formula>),
    Exists(Vec<Variable>, Box<Formula>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Variable {
    pub id: usize,
    pub sort: Sort,
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "X{}", self.id)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CNF(Vec<Vec<RichFormula>>);

use super::builtins::functions::{f_and, f_false, f_or, f_true, AND, FALSE, NOT, OR, TRUE};
impl From<CNF> for RichFormula {
    fn from(cnf: CNF) -> Self {
        from_conjunction(cnf.0.into_iter().map(|c| from_disjunction(c.into_iter())))
    }
}

fn from_disjunction(mut dis: impl Iterator<Item = RichFormula>) -> RichFormula {
    match dis.next() {
        None => f_true(),
        Some(f) => dis.fold(f, f_or),
    }
}

fn from_conjunction(mut dis: impl Iterator<Item = RichFormula>) -> RichFormula {
    match dis.next() {
        None => f_false(),
        Some(f) => dis.fold(f, f_and),
    }
}

macro_rules! var {
    ($id:pat, $sort:pat) => {
        crate::formula::formula::RichFormula::Var(crate::formula::formula::Variable {
            id: $id,
            sort: $sort,
        })
    };
    ($id:expr; $sort:expr) => {
        crate::formula::formula::RichFormula::Var(crate::formula::formula::Variable {
            id: $id,
            sort: $sort,
        })
    };
}

macro_rules! fun {
    ($f:pat, $args:pat) => {
        crate::formula::formula::RichFormula::Fun($f, $args)
    };
    ($f:expr; $($args:expr),*) => {
        crate::formula::formula::RichFormula::Fun($f.clone(), vec![$($args,)*])
    };
}

macro_rules! quant {
    ($f:pat, $args:pat) => {
        crate::formula::formula::RichFormula::Quantifier($f, $args)
    };
    ($f:expr; $($args:expr),*) => {
        crate::formula::formula::RichFormula::Quantifier($f.clone(), vec![$($args,)*])
    };
}
pub(crate) use {fun, quant, var};

impl RichFormula {
    pub fn get_sort(&self) -> &Sort {
        match self {
            var!(_, s) => s,
            fun!(f, _) => f.get_output_sort(),
            quant!(q, _) => q.get_output_sort(),
        }
    }

    pub fn get_free_vars(&self) -> Vec<&Variable> {
        let mut r = Vec::new();
        let mut bounded = Vec::new();

        fn aux<'a>(bounded: &mut Vec<&'a Variable>, r: &mut Vec<&'a Variable>, t: &'a RichFormula) {
            match t {
                RichFormula::Fun(_, args) => args.iter().for_each(|f| aux(bounded, r, f)),
                RichFormula::Var(v) if !bounded.contains(&v) => r.push(v),
                RichFormula::Quantifier(q, args) => {
                    let vars = q.get_variables();
                    let n = vars.len();
                    bounded.extend(vars.into_iter());
                    args.iter().for_each(|f| aux(bounded, r, f));
                    bounded.truncate(bounded.len() - n);
                }
                _ => {}
            }
        }
        aux(&mut bounded, &mut r, self);
        r
    }

    pub fn simplify(self) -> RichFormula {
        match self {
            RichFormula::Fun(f, args) => {
                let truef = fun!(TRUE;);
                let falsef = fun!(FALSE;);

                if f.eq(&AND) {
                    let args: Vec<_> = args.into_iter().map(Self::simplify).collect();
                    if args.contains(&falsef) {
                        falsef
                    } else if args[0] == truef {
                        args.into_iter().nth(1).unwrap()
                    } else if args[1] == truef {
                        args.into_iter().nth(0).unwrap()
                    } else {
                        RichFormula::Fun(f, args)
                    }
                } else if f.eq(&OR) {
                    let args: Vec<_> = args.into_iter().map(Self::simplify).collect();
                    if args.contains(&truef) {
                        truef
                    } else if args[0] == falsef {
                        args.into_iter().nth(1).unwrap()
                    } else if args[1] == falsef {
                        args.into_iter().nth(0).unwrap()
                    } else {
                        RichFormula::Fun(f, args)
                    }
                } else if f.eq(&NOT) {
                    match args.into_iter().nth(0).unwrap() {
                        RichFormula::Fun(f, args) => {
                            if f.eq(&AND) {
                                RichFormula::Fun(OR.clone(), args).simplify()
                            } else if f.eq(&OR) {
                                RichFormula::Fun(AND.clone(), args).simplify()
                            } else {
                                RichFormula::Fun(f, args).simplify()
                            }
                        }
                        RichFormula::Quantifier(_, _) => todo!(),
                        f => f,
                    }
                } else {
                    let args: Vec<_> = args.into_iter().map(Self::simplify).collect();
                    RichFormula::Fun(f, args)
                }
            }
            _ => self,
        }
    }
}

impl Variable {
    pub fn new(id: usize, sort: Sort) -> Self {
        Self { id, sort }
    }
}

impl CNF {
    pub fn new(f: Vec<Vec<RichFormula>>) -> Self {
        CNF(f)
    }
}
