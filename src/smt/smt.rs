use std::fmt::{self};

use itertools::Itertools;

use crate::formula::{
    builtins::functions::{AND_NAME, B_IF_THEN_ELSE_NAME, IMPLIES, NOT, OR_NAME},
    env::Environement,
    formula::{RichFormula, Variable},
    function::Function,
    quantifier::Quantifier,
    sort::Sort,
};

use super::macros::sfun;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum SmtFormula {
    Var(Variable),
    Fun(Function, Vec<SmtFormula>),
    Forall(Vec<Variable>, Box<SmtFormula>),
    Exists(Vec<Variable>, Box<SmtFormula>),

    And(Vec<SmtFormula>),
    Or(Vec<SmtFormula>),
    Eq(Vec<SmtFormula>),
    Neq(Vec<SmtFormula>),

    Ite(Box<SmtFormula>, Box<SmtFormula>, Box<SmtFormula>),
}

pub fn implies(env: &Environement, a: SmtFormula, b: SmtFormula) -> SmtFormula {
    sfun!(IMPLIES(env); a, b)
}

pub fn not(env: &Environement, a: SmtFormula) -> SmtFormula {
    sfun!(NOT(env); a)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Smt {
    Assert(SmtFormula),
    AssertTh(SmtFormula),
    AssertNot(SmtFormula),
    DeclareFun(Function),
    DeclareSort(Sort),

    DeclareSubtermRelation(Function, Vec<Function>),

    DeclareRewrite {
        rewrite_fun: RewriteKind,
        vars: Vec<Variable>,
        lhs: Box<SmtFormula>,
        rhs: Box<SmtFormula>,
    },

    DeclareDatatypes {
        sorts: Vec<Sort>,
        cons: Vec<Vec<SmtCons>>,
    },

    CheckSat,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtCons {
    pub fun: Function,
    pub dest: Vec<Function>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RewriteKind {
    Bool,
    Other(Function),
}

impl fmt::Display for SmtFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtFormula::Var(v) => v.fmt(f),
            SmtFormula::Fun(fun, args) => {
                if args.len() > 0 {
                    write!(f, "({} ", fun.name())?;
                    for arg in args {
                        write!(f, "{} ", arg)?;
                    }
                    write!(f, ")")
                } else {
                    write!(f, "{} ", fun.name())
                }
            }
            SmtFormula::Forall(vars, formula) | SmtFormula::Exists(vars, formula)
                if vars.is_empty() =>
            {
                formula.fmt(f)
            }
            SmtFormula::Forall(vars, formula) => {
                write!(f, "(forall (")?;
                for v in vars {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                write!(f, ") {})", formula)
            }
            SmtFormula::Exists(vars, formula) => {
                write!(f, "(exists (")?;
                for v in vars {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                write!(f, ") {})", formula)
            }
            SmtFormula::And(args) if args.is_empty() => write!(f, "true"),
            SmtFormula::And(args) => fun_list_fmt(f, "and", args.iter()),
            SmtFormula::Or(args) if args.is_empty() => write!(f, "false"),
            SmtFormula::Or(args) => fun_list_fmt(f, "or", args.iter()),
            SmtFormula::Eq(args) => fun_list_fmt(f, "=", args.iter()),
            SmtFormula::Neq(args) => fun_list_fmt(f, "distinct", args.iter()),
            SmtFormula::Ite(c, r, l) => {
                write!(f, "(ite {} {} {})", c, r, l)
            }
        }
    }
}

impl fmt::Display for Smt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Smt::Assert(e) => write!(f, "(assert {})", e),
            Smt::AssertTh(e) => write!(f, "(assert-theory {})", e),
            Smt::AssertNot(e) => write!(f, "(assert-not {})", e),
            Smt::DeclareFun(fun) => {
                write!(f, "(declare-fun {} (", fun.name())?;
                for s in fun.input_sorts_iter() {
                    write!(f, "{} ", s)?;
                }
                write!(f, ") {})", fun.get_output_sort())
            }
            Smt::DeclareSort(sort) => write!(f, "(declare-sort {} 0)", sort),
            Smt::DeclareSubtermRelation(fun, funs) => {
                write!(f, "(declare-subterm-relation {} ", fun.name())?;
                for fun in funs {
                    write!(f, "{} ", fun.name())?;
                }
                write!(f, ")")
            }
            Smt::DeclareRewrite {
                rewrite_fun,
                vars,
                lhs,
                rhs,
            } => {
                write!(f, "(declare-rewrite (forall (")?;
                for v in vars {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                let op = match rewrite_fun {
                    RewriteKind::Bool => "=>",
                    RewriteKind::Other(f) => f.name(),
                };
                write!(f, ") ({} {} {})))", op, lhs, rhs)
            }
            Smt::DeclareDatatypes { sorts, cons } => {
                write!(f, "(declare-datatypes\n")?;
                // name of types
                write!(f, "\t(")?;
                for s in sorts {
                    write!(f, "({} 0) ", s)?;
                }
                write!(f, ")\n\t(\n")?;

                // cons
                for (j, vc) in cons.iter().enumerate() {
                    write!(f, "\t\t(\n")?;
                    for c in vc {
                        assert_eq!(sorts[j], c.fun.get_output_sort());

                        write!(f, "\t\t\t({} ", c.fun.name())?;

                        for (i, s) in c.fun.get_input_sorts().iter().enumerate() {
                            write!(f, "({} {}) ", c.dest.get(i).unwrap().name(), s)?;
                        }
                        write!(f, ")\n")?;
                    }
                    write!(f, "\t\t)\n")?;
                }
                write!(f, "\t)\n)")
            }

            Smt::CheckSat => write!(f, "(check-sat)"),
        }
    }
}

fn fun_list_fmt<I: Iterator<Item = impl fmt::Display>>(
    f: &mut fmt::Formatter,
    str: &str,
    iter: I,
) -> fmt::Result {
    write!(f, "({} ", str)?;
    for e in iter {
        write!(f, "{} ", e)?;
    }
    write!(f, ")")
}

impl From<&RichFormula> for SmtFormula {
    fn from(f: &RichFormula) -> Self {
        match f {
            RichFormula::Var(v) => v.into(),

            RichFormula::Fun(f, args) => {
                let mut iter = args.into_iter().map(Into::into);
                match f.name() {
                    AND_NAME => SmtFormula::And(iter.collect()),
                    OR_NAME => SmtFormula::Or(iter.collect()),
                    // NOT_NAME => SmtFormula::Not(iter.next().unwrap()),
                    B_IF_THEN_ELSE_NAME => {
                        let (c, l, r) = iter.next_tuple().unwrap();
                        SmtFormula::Ite(Box::new(c), Box::new(l), Box::new(r))
                    }
                    _ => SmtFormula::Fun(f.clone(), iter.collect()),
                }
            }
            RichFormula::Quantifier(Quantifier::Exists { variables }, args) => SmtFormula::Exists(
                variables.clone(),
                Box::new(args.into_iter().next().unwrap().into()),
            ),
            RichFormula::Quantifier(Quantifier::Forall { variables }, args) => SmtFormula::Forall(
                variables.clone(),
                Box::new(args.into_iter().next().unwrap().into()),
            ),
            RichFormula::Quantifier(_, _) => panic!("unsuported quantifier: {:?}", f),
        }
    }
}

impl From<RichFormula> for SmtFormula {
    fn from(f: RichFormula) -> Self {
        SmtFormula::from(&f)
    }
}

impl From<&Variable> for SmtFormula {
    fn from(v: &Variable) -> Self {
        v.clone().into()
    }
}
impl From<Variable> for SmtFormula {
    fn from(v: Variable) -> Self {
        SmtFormula::Var(v)
    }
}

impl Smt {
    pub fn rewrite_to_assert(self, env: &Environement) -> Self {
        match self {
            Self::DeclareRewrite {
                rewrite_fun: RewriteKind::Bool,
                vars,
                lhs,
                rhs,
            } => Smt::Assert(SmtFormula::Forall(vars, Box::new(implies(env, *lhs, *rhs)))),
            Self::DeclareRewrite {
                rewrite_fun: RewriteKind::Other(_),
                vars,
                lhs,
                rhs,
            } => Smt::Assert(SmtFormula::Forall(
                vars,
                Box::new(SmtFormula::Eq(vec![*lhs, *rhs])),
            )),
            _ => self,
        }
    }
}
