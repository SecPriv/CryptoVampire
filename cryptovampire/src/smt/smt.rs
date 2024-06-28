use std::{
    fmt::{self},
    sync::Arc,
};

use cryptovampire_lib::{
    environement::{
        environement::Environement,
        traits::{KnowsRealm, Realm},
    },
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
    SubtermKind,
};

use utils::implvec;

use self::display::{SmtDisplayer, SmtEnv};

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
    AssertGround {
        sort: Sort<'bump>,
        formula: SmtFormula<'bump>,
    },
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

mod display;

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
    pub fn from_arichformula(
        /* env: &Environement<'bump>,*/ formula: &RichFormula<'bump>,
    ) -> Self {
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
                            // Connective::Iff => SmtFormula::Eq(args),
                        },
                    },
                    // InnerFunction::Invalid(_) => unreachable!("the function is invalid")
                }
            }
        }
    }

    pub fn default_display(&self) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: Realm::Symbolic,
            },
            content: self,
        }
    }

    pub fn as_display(self, env: &impl KnowsRealm) -> impl fmt::Display + 'bump {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }

    pub fn as_display_ref(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }

    fn prop<D, T>(&self, disp: SmtDisplayer<D, T>) -> SmtDisplayer<D, &Self> {
        disp.propagate(&self)
    }
}

impl<'bump> Smt<'bump> {
    pub fn from_axiom(env: &Environement<'bump>, ax: Axiom<'bump>) -> Self {
        match ax {
            Axiom::Comment(str) => Smt::Comment(str.into()),
            Axiom::Base { formula } => {
                Smt::Assert(SmtFormula::from_arichformula(
                    /* env, */ formula.as_ref(),
                ))
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
                            // SmtFormula::Implies(Box::new(pre), Box::new(post))
                            SmtFormula::Eq(vec![pre, post])
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
            Axiom::Ground { sort, formula } => {
                if env.use_assert_ground() {
                    Smt::AssertGround {
                        sort,
                        formula: SmtFormula::from_arichformula(&formula),
                    }
                } else {
                    Smt::Assert(SmtFormula::from_arichformula(formula.as_ref()))
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

    pub fn as_display(self, env: &impl KnowsRealm) -> impl fmt::Display + 'bump {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }

    pub fn as_display_ref(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }

    fn prop<D, T>(&self, disp: SmtDisplayer<D, T>) -> SmtDisplayer<D, &Self> {
        disp.propagate(&self)
    }

    /// Returns `true` if the smt is [`Assert`].
    ///
    /// [`Assert`]: Smt::Assert
    #[must_use]
    pub fn is_any_assert(&self) -> bool {
        matches!(
            self,
            Self::Assert(..) | Self::AssertNot(..) | Self::AssertTh(..)
        )
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

    pub fn as_diplay(&self, env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer {
            env: SmtEnv {
                realm: env.get_realm(),
            },
            content: self,
        }
    }
}
