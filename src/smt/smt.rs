use std::{
    fmt::{self, Display},
    sync::Arc,
};

use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{
            axioms::{Axiom, Rewrite, RewriteKind},
            declare::Declaration,
            GeneralFile,
        },
        formula::RichFormula,
        function::{
            inner::booleans::{Booleans, Connective},
            Function, InnerFunction,
        },
        quantifier::Quantifier,
        sort::Sort,
        variable::Variable,
    },
    implvec,
    problem::subterm::kind::SubtermKind,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtFile<'bump> {
    content: Vec<Smt<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum SmtFormula<'bump> {
    Var(Variable<'bump>),
    Fun(Function<'bump>, Vec<SmtFormula<'bump>>),
    Forall(Arc<[Variable<'bump>]>, Box<SmtFormula<'bump>>),
    Exists(Arc<[Variable<'bump>]>, Box<SmtFormula<'bump>>),

    True,
    False,
    And(Vec<SmtFormula<'bump>>),
    Or(Vec<SmtFormula<'bump>>),
    Eq(Vec<SmtFormula<'bump>>),
    Neq(Vec<SmtFormula<'bump>>),
    Not(Box<SmtFormula<'bump>>),
    Implies(Box<SmtFormula<'bump>>, Box<SmtFormula<'bump>>),

    Subterm(
        Function<'bump>,
        Box<SmtFormula<'bump>>,
        Box<SmtFormula<'bump>>,
    ),

    Ite(
        Box<SmtFormula<'bump>>,
        Box<SmtFormula<'bump>>,
        Box<SmtFormula<'bump>>,
    ),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Smt<'bump> {
    Assert(SmtFormula<'bump>),
    AssertTh(SmtFormula<'bump>),
    AssertNot(SmtFormula<'bump>),
    DeclareFun(Function<'bump>),
    DeclareSort(Sort<'bump>),
    DeclareSortAlias {
        from: Sort<'bump>,
        to: Sort<'bump>,
    },

    DeclareSubtermRelation(Function<'bump>, Vec<Function<'bump>>),

    DeclareRewrite {
        rewrite_fun: RewriteKind<'bump>,
        vars: Arc<[Variable<'bump>]>,
        lhs: Box<SmtFormula<'bump>>,
        rhs: Box<SmtFormula<'bump>>,
    },

    DeclareDatatypes {
        sorts: Vec<Sort<'bump>>,
        cons: Vec<Vec<SmtCons<'bump>>>,
    },
    Comment(String),

    CheckSat,
    GetProof,
    SetOption(String, String),
    SetLogic(String),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtCons<'bump> {
    pub fun: Function<'bump>,
    pub dest: Vec<Function<'bump>>,
}

impl<'bump> fmt::Display for SmtFormula<'bump> {
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
                for v in vars.into_iter() {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                write!(f, ") {})", formula)
            }
            SmtFormula::Exists(vars, formula) => {
                write!(f, "(exists (")?;
                for v in vars.into_iter() {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                write!(f, ") {})", formula)
            }
            SmtFormula::True => write!(f, "true"),
            SmtFormula::False => write!(f, "false"),
            SmtFormula::And(args) if args.is_empty() => SmtFormula::True.fmt(f),
            SmtFormula::And(args) => fun_list_fmt(f, "and", args.iter()),
            SmtFormula::Or(args) if args.is_empty() => SmtFormula::False.fmt(f),
            SmtFormula::Or(args) => fun_list_fmt(f, "or", args.iter()),
            SmtFormula::Eq(args) | SmtFormula::Neq(args) if args.len() <= 1 => {
                SmtFormula::True.fmt(f)
            }
            SmtFormula::Eq(args) => fun_list_fmt(f, "=", args.iter()),
            SmtFormula::Neq(args) => fun_list_fmt(f, "distinct", args.iter()),
            SmtFormula::Ite(c, r, l) => {
                write!(f, "(ite {} {} {})", c, r, l)
            }
            SmtFormula::Implies(a, b) => write!(f, "(=> {} {})", a, b),
            SmtFormula::Subterm(fun, a, b) => write!(f, "(subterm {} {} {})", fun.name(), a, b),
            SmtFormula::Not(a) => write!(f, "(not {})", a),
        }
    }
}

impl<'bump> fmt::Display for Smt<'bump> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Smt::Assert(e) => writeln!(f, "(assert {})", e),
            Smt::AssertTh(e) => writeln!(f, "(assert-theory {})", e),
            Smt::AssertNot(e) => writeln!(f, "(assert-not {})", e),
            Smt::DeclareFun(fun) => {
                write!(f, "(declare-fun {} (", fun.name())?;
                for s in fun.fast_insort().expect(&format!(
                    "all function defined here have known sort: {}",
                    fun.name()
                )) {
                    write!(f, "{} ", s.name())?;
                }
                writeln!(f, ") {})", fun.fast_outsort().unwrap())
            }
            Smt::DeclareSort(sort) => writeln!(f, "(declare-sort {} 0)", sort),
            Smt::DeclareSortAlias { from, to } => {
                writeln!(f, "(define-sort {} () {})", to.name(), from.name())
            }
            Smt::DeclareSubtermRelation(fun, funs) => {
                write!(f, "(declare-subterm-relation {} ", fun.name())?;
                for fun in funs {
                    write!(f, "{} ", fun.name())?;
                }
                writeln!(f, ")")
            }
            Smt::DeclareRewrite {
                rewrite_fun,
                vars,
                lhs,
                rhs,
            } => {
                write!(f, "(declare-rewrite (forall (")?;
                for v in vars.into_iter() {
                    write!(f, "({} {}) ", v, v.sort)?;
                }
                let op = match rewrite_fun {
                    RewriteKind::Bool => "=>".into(),
                    RewriteKind::Other(f) => f.name(),
                };
                writeln!(f, ") ({} {} {})))", op, lhs, rhs)
            }
            Smt::DeclareDatatypes { sorts, cons } => {
                write!(f, "(declare-datatypes\n")?;
                // name of types
                write!(f, "\t(")?;
                for s in sorts.into_iter() {
                    write!(f, "({} 0) ", s)?;
                }
                write!(f, ")\n\t(\n")?;

                // cons
                for (j, vc) in cons.iter().enumerate() {
                    write!(f, "\t\t(\n")?;
                    for c in vc {
                        assert_eq!(sorts[j], c.fun.fast_outsort().unwrap());

                        write!(f, "\t\t\t({} ", c.fun.name())?;

                        for (i, s) in c.fun.fast_insort().expect("todo").iter().enumerate() {
                            write!(f, "({} {}) ", c.dest.get(i).unwrap().name(), s)?;
                        }
                        write!(f, ")\n")?;
                    }
                    write!(f, "\t\t)\n")?;
                }
                writeln!(f, "\t)\n)")
            }

            Smt::CheckSat => writeln!(f, "(check-sat)"),
            Smt::Comment(s) => writeln!(f, "\n; {}\n", s),
            Smt::GetProof => writeln!(f, "(get-proof)"),
            Smt::SetOption(option, arg) => writeln!(f, "(set-option :{} {})", option, arg),
            Smt::SetLogic(logic) => writeln!(f, "(set-logic {})", logic),
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

macro_rules! unpack_args {
    ([$($arg:ident),*] = $args:expr; $do:block) => {{
        let mut iter = $args.into_iter();
        $(
            let $arg = if let Some(tmp) = iter.next() {
                tmp
            } else {
                panic!("not enough arguments")
            };
        )*
        assert!(iter.next().is_none(), "too many arguments");
        $do
    }};
}

impl<'bump> SmtFormula<'bump> {
    pub fn from_arichformula(/* env: &Environement<'bump>,*/ formula: &RichFormula<'bump>) -> Self {
        match formula {
            RichFormula::Var(v) => SmtFormula::Var(*v),
            RichFormula::Quantifier(q, arg) => match q {
                Quantifier::Exists { variables } => SmtFormula::Exists(
                    variables.clone(),
                    Box::new(Self::from_arichformula(/* env, */ arg.as_ref())),
                ),
                Quantifier::Forall { variables } => SmtFormula::Forall(
                    variables.clone(),
                    Box::new(Self::from_arichformula(/* env, */ arg.as_ref())),
                ),
            },
            RichFormula::Fun(f, args) => {
                let mut args = args
                    .into_iter()
                    .map(|f| Self::from_arichformula(/* env, */ f.as_ref()))
                    .collect();

                match f.as_inner() {
                    InnerFunction::TermAlgebra(_)
                    // | InnerFunction::Nonce(_)
                    | InnerFunction::Step(_)
                    | InnerFunction::Predicate(_)
                    | InnerFunction::Tmp(_)
                    | InnerFunction::Skolem(_)
                    | InnerFunction::Name(_)
                    | InnerFunction::EvaluatedFun(_)
                    | InnerFunction::Evaluate(_) => SmtFormula::Fun(*f, args),
                    InnerFunction::Subterm(subterm) => {
                        let kind = subterm.kind();

                        match kind {
                            SubtermKind::Regular(_) => SmtFormula::Fun(*f, args),
                            SubtermKind::Vampire(_) => {
                                unpack_args!([a, b] =  args; {
                                    SmtFormula::Subterm(*f, Box::new(a), Box::new(b))
                                })
                            }
                        }
                    }
                    InnerFunction::IfThenElse(_) => {
                        unpack_args!([c, l, r] = args; {
                            SmtFormula::Ite(Box::new(c), Box::new(l), Box::new(r))
                        })
                    }
                    InnerFunction::Bool(c) => match c {
                        Booleans::Equality(_) => SmtFormula::Eq(args),
                        Booleans::Connective(c) => match c {
                            Connective::True => SmtFormula::True,
                            Connective::False => SmtFormula::False,
                            Connective::And => SmtFormula::And(args),
                            Connective::Or => SmtFormula::Or(args),
                            Connective::Not => SmtFormula::Not(Box::new(args.pop().unwrap())),
                            Connective::Implies => {
                                unpack_args!([a, b] = args; {
                                    SmtFormula::Implies(Box::new(a), Box::new(b))
                                })
                            }
                            Connective::Iff => SmtFormula::Eq(args),
                        },
                    },
                    // InnerFunction::Invalid(_) => unreachable!("the function is invalid")
                }
            }
        }
    }
}

impl<'bump> Smt<'bump> {
    pub fn from_axiom(env: &Environement<'bump>, ax: Axiom<'bump>) -> Self {
        match ax {
            Axiom::Comment(str) => Smt::Comment(str.into()),
            Axiom::Base { formula } => {
                Smt::Assert(SmtFormula::from_arichformula(/* env, */ formula.as_ref()))
            }
            Axiom::Theory { formula } => {
                let f = SmtFormula::from_arichformula(/* env, */ formula.as_ref());
                if env.use_assert_theory() {
                    Smt::AssertTh(f)
                } else {
                    Smt::Assert(f)
                }
            }
            Axiom::Query { formula } => {
                let f = SmtFormula::from_arichformula(/* env, */ formula.as_ref());
                if env.use_assert_not() {
                    Smt::AssertNot(f)
                } else {
                    Smt::Assert(SmtFormula::Not(Box::new(f)))
                }
            }
            Axiom::Rewrite { rewrite } => {
                let Rewrite {
                    kind,
                    vars,
                    pre,
                    post,
                } = *rewrite;
                let pre = SmtFormula::from_arichformula(/* env, */ pre.as_ref());
                let post = SmtFormula::from_arichformula(/* env, */ post.as_ref());
                if env.no_rewrite() {
                    Smt::Assert(SmtFormula::Forall(
                        vars,
                        Box::new(if kind == RewriteKind::Bool {
                            SmtFormula::Implies(Box::new(pre), Box::new(post))
                        } else {
                            SmtFormula::Eq(vec![pre, post])
                        }),
                    ))
                } else {
                    Smt::DeclareRewrite {
                        rewrite_fun: kind,
                        vars,
                        lhs: Box::new(pre),
                        rhs: Box::new(post),
                    }
                }
            }
        }
    }

    pub fn from_declaration(_env: &Environement<'bump>, dec: Declaration<'bump>) -> Self {
        match dec {
            Declaration::Sort(s) => Self::DeclareSort(s),
            Declaration::FreeFunction(fun) => Self::DeclareFun(fun),
            Declaration::DataTypes(dt) => {
                let (sorts, cons) = dt
                    .into_iter()
                    .map(|dt| {
                        (
                            dt.sort,
                            dt.constructor_destructors
                                .into_iter()
                                .map(|cd| SmtCons {
                                    fun: cd.constructor,
                                    dest: cd.destructor,
                                })
                                .collect(),
                        )
                    })
                    .unzip();
                Self::DeclareDatatypes { sorts, cons }
            }
            Declaration::Subterm(sub) => {
                Self::DeclareSubtermRelation(sub.function, sub.comutative_functions)
            }
            Declaration::SortAlias { from, to } => Self::DeclareSortAlias { from, to },
        }
    }
}

impl<'bump> SmtFile<'bump> {
    pub fn new(content: implvec!(Smt<'bump>)) -> Self {
        Self {
            content: content.into_iter().collect(),
        }
    }

    pub fn content(&self) -> &[Smt<'bump>] {
        self.content.as_ref()
    }

    pub fn content_mut(&mut self) -> &mut Vec<Smt<'bump>> {
        &mut self.content
    }

    pub fn from_general_file(
        env: &Environement<'bump>,
        GeneralFile {
            assertions,
            declarations,
        }: GeneralFile<'bump>,
    ) -> Self {
        let declarations = declarations
            .into_iter()
            .map(|d| Smt::from_declaration(env, d));
        let assertions = assertions.into_iter().map(|ax| Smt::from_axiom(env, ax));
        let other = [Smt::CheckSat];

        let content = itertools::chain!(declarations, assertions, other).collect();
        Self { content }
    }
}

impl<'bump> Display for SmtFile<'bump> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if cfg!(debug_assertions) {
            self.content
                .iter()
                .filter_map(|smt| match smt {
                    Smt::DeclareFun(f) => Some(f),
                    _ => None,
                })
                .for_each(|f| println!("trying to define {}", f.name()))
        }

        self.content.iter().try_for_each(|smt| writeln!(f, "{smt}"))
    }
}
