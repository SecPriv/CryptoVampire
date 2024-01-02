use std::fmt::{self};

use itertools::Itertools;

use crate::{
    formula::{
        builtins::{
            functions::{AND_NAME, B_IF_THEN_ELSE_NAME, IMPLIES, NOT, OR_NAME},
            types::BOOL,
        },
        env::Environement,
        formula::{RichFormula, Variable},
        function::Function,
        quantifier::Quantifier,
        sort::Sort,
    },
    smt::macros::svar,
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
    Comment(String),

    CheckSat,
    GetProof,
    SetOption(String, String),
    SetLogic(String),
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
            SmtFormula::Eq(args) | SmtFormula::Neq(args) if args.len() <= 1 => write!(f, "true"),
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
            Smt::Comment(s) => write!(f, "\n; {}\n", s),
            Smt::GetProof => write!(f, "(get-proof)"),
            Smt::SetOption(option, arg) => write!(f, "(set-option :{} {})", option, arg),
            Smt::SetLogic(logic) => write!(f, "(set-logic {})", logic),
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

impl SmtFormula {
    /// Gets rid of as many exists (or hidden exists) quantifiers as possible.
    /// Some may remain if they are too tricky to soundly remove
    pub fn skolemnise(
        self,
        env: &mut Environement,
        negative: bool,
        free_vars: &[Variable],
    ) -> (Self, Vec<Function>) {
        let mut skolems = Vec::new();
        let mut fv = free_vars.into();

        struct SC {
            not: Function,
            bool: Sort,
            implies: Function,
        }
        let db = SC {
            not: NOT(env).clone(),
            bool: BOOL(env).clone(),
            implies: IMPLIES(env).clone(),
        };

        fn aux(
            f: SmtFormula,
            env: &mut Environement,
            negative: bool,
            skolems: &mut Vec<Function>,
            db: &SC,
            fv: &mut Vec<Variable>,
        ) -> SmtFormula {
            match (negative, f) {
                (negative, SmtFormula::Fun(fun, args)) if fun == db.not => SmtFormula::Fun(
                    fun,
                    vec![aux(
                        args.into_iter().next().unwrap(),
                        env,
                        !negative,
                        skolems,
                        db,
                        fv,
                    )],
                ),
                (negative, SmtFormula::Fun(fun, args)) if fun == db.implies => {
                    let mut iter = args.into_iter();
                    let premise = iter.next().unwrap();
                    let conclusion = iter.next().unwrap();
                    SmtFormula::Fun(
                        fun,
                        vec![
                            aux(premise, env, !negative, skolems, db, fv),
                            aux(conclusion, env, negative, skolems, db, fv),
                        ],
                    )
                }

                (_, SmtFormula::Fun(fun, args)) if !fun.get_input_sorts().contains(&db.bool) => {
                    SmtFormula::Fun(
                        fun,
                        args.into_iter()
                            .map(|arg| aux(arg, env, negative, skolems, db, fv))
                            .collect(),
                    )
                }
                (true, SmtFormula::Forall(vars, arg)) | (false, SmtFormula::Exists(vars, arg)) => {
                    let nvars = vars
                        .iter()
                        .map(|v| env.add_skolem(fv.iter().map(|v2| &v2.sort), &v.sort))
                        .collect_vec();
                    skolems.extend(nvars.iter().cloned());
                    let fs = nvars
                        .into_iter()
                        .map(|fun| sfun!(fun, fv.iter().map(|v| svar!(v.clone())).collect()))
                        .collect_vec();
                    let vars = vars.into_iter().map(|v| v.id).collect_vec();
                    let arg = arg.partial_substitution(&vars, &fs);
                    aux(arg, env, negative, skolems, db, fv)
                }
                (_, SmtFormula::Forall(vars, arg)) => {
                    fv.extend(vars.iter().cloned());
                    let arg = Box::new(aux(*arg, env, negative, skolems, db, fv));
                    // gets rid of the free variable of this quantifier
                    fv.truncate(fv.len() - vars.len());
                    SmtFormula::Forall(vars, arg)
                }
                (_, SmtFormula::Exists(vars, arg)) => {
                    fv.extend(vars.iter().cloned());
                    let arg = Box::new(aux(*arg, env, negative, skolems, db, fv));
                    // gets rid of the free variable of this quantifier
                    fv.truncate(fv.len() - vars.len());
                    SmtFormula::Exists(vars, arg)
                }
                (_, SmtFormula::And(args)) => SmtFormula::And(
                    args.into_iter()
                        .map(|f| aux(f, env, negative, skolems, db, fv))
                        .collect(),
                ),
                (_, SmtFormula::Or(args)) => SmtFormula::Or(
                    args.into_iter()
                        .map(|f| aux(f, env, negative, skolems, db, fv))
                        .collect(),
                ),
                (_, f) => f,
            }
        }

        let result = aux(self, env, negative, &mut skolems, &db, &mut fv);
        (result, skolems)
    }

    pub fn map<F>(self, f: &F) -> Self
    where
        F: Fn(Self) -> Self,
    {
        match self {
            SmtFormula::Var(_) => f(self),
            SmtFormula::Fun(fun, args) => f(SmtFormula::Fun(
                fun,
                args.into_iter().map(|arg| arg.map(f)).collect(),
            )),
            SmtFormula::Forall(vars, arg) => f(Self::Forall(vars, Box::new(f(arg.map(f))))),
            SmtFormula::Exists(vars, arg) => f(Self::Exists(vars, Box::new(f(arg.map(f))))),
            SmtFormula::And(arg) => f(Self::And(arg.into_iter().map(|x| x.map(f)).collect())),
            SmtFormula::Or(arg) => f(Self::Or(arg.into_iter().map(|x| x.map(f)).collect())),
            SmtFormula::Eq(arg) => f(Self::Eq(arg.into_iter().map(|x| x.map(f)).collect())),
            SmtFormula::Neq(arg) => f(Self::Neq(arg.into_iter().map(|x| x.map(f)).collect())),
            SmtFormula::Ite(c, l, r) => {
                let c = Box::new(f(*c));
                let r = Box::new(f(*r));
                let l = Box::new(f(*l));
                f(Self::Ite(c, r, l))
            }
        }
    }

    pub fn partial_substitution(self, vars: &[usize], fs: &[SmtFormula]) -> Self {
        debug_assert_eq!(vars.len(), fs.len());

        let idx = |v| vars.iter().position(|&var| var == v);

        self.map(&{
            |f| match f {
                Self::Var(v) => {
                    if let Some(i) = idx(v.id) {
                        fs[i].clone()
                    } else {
                        Self::Var(v)
                    }
                }
                _ => f,
            }
        })
    }
}
