use std::fmt::{self};

use crate::formula::{
    builtins::functions::IMPLIES,
    formula::{fun, Variable},
    function::Function,
    sort::Sort,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
        cons: Vec<SmtCons>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SmtCons {
    fun: Function,
    dest: Vec<Function>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RewriteKind {
    Bool,
    Other(Function),
}

impl fmt::Display for SmtFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtFormula::Var(v) => v.fmt(f),
            SmtFormula::Fun(fun, args) => {
                write!(f, "({} ", fun.name())?;
                for arg in args {
                    write!(f, "{} ", arg)?;
                }
                write!(f, ")")
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
            SmtFormula::And(args) => fun_list_fmt(f, "and", args.iter()),
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
                for s in fun.get_input_sorts() {
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
                write!(f, "declare-rewrite (forall ")?;
                for v in vars {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                let op = match rewrite_fun {
                    RewriteKind::Bool => "=>",
                    RewriteKind::Other(f) => f.name(),
                };
                write!(f, ") ({} {} {}))", op, lhs, rhs)
            }
            Smt::DeclareDatatypes { sorts, cons } => {
                write!(f, "(declare-datatypes ")?;
                // name of types
                write!(f, "(")?;
                for s in sorts {
                    write!(f, "({} 0) ", s)?;
                }
                write!(f, ") (")?;

                // cons
                for (j, c) in cons.iter().enumerate() {
                    assert_eq!(&sorts[j], c.fun.get_output_sort());

                    write!(f, "({}", c.fun.name())?;

                    for (i, s) in c.fun.get_input_sorts().iter().enumerate() {
                        write!(f, "({} {})", c.dest.get(i).unwrap().name(), s)?;
                    }
                    write!(f, ")")?;
                }
                write!(f, "))")
            }
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
