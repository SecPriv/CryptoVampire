use std::{
    fmt::{self},
    sync::Arc,
};

use utils::implvec;

use self::display::{SmtDisplayer, SmtEnv};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtFile<V, F, S, Rw> {
    content: Vec<Smt<V, F, S, Rw>>,
}

#[non_exhaustive]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum SmtFormula<V, F> {
    Var(V),
    Fun(F, Vec<SmtFormula<V, F>>),
    Forall(Vec<V>, Box<SmtFormula<V, F>>),
    Exists(Arc<[V]>, Box<SmtFormula<V, F>>),

    True,
    False,
    And(Vec<SmtFormula<V, F>>),
    Or(Vec<SmtFormula<V, F>>),
    Eq(Vec<SmtFormula<V, F>>),
    Neq(Vec<SmtFormula<V, F>>),
    Not(Box<SmtFormula<V, F>>),
    Implies(Box<SmtFormula<V, F>>, Box<SmtFormula<V, F>>),

    Subterm(
        F,
        Box<SmtFormula<V, F>>,
        Box<SmtFormula<V, F>>,
    ),

    Ite(
        Box<SmtFormula<V, F>>,
        Box<SmtFormula<V, F>>,
        Box<SmtFormula<V, F>>,
    ),
}

#[non_exhaustive]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Smt<V, F, S, Rw>{
    Assert(SmtFormula<V, F>),
    AssertTh(SmtFormula<V, F>),
    AssertGround {
        sort: S,
        formula: SmtFormula<V, F>,
    },
    AssertNot(SmtFormula<V, F>),
    DeclareFun(F),
    DeclareSort(S),
    DeclareSortAlias {
        from: S,
        to: S,
    },

    DeclareSubtermRelation(F, Vec<V>),

    DeclareRewrite {
        rewrite_fun: Rw,
        vars: Arc<[V]>,
        lhs: Box<SmtFormula<V, F>>,
        rhs: Box<SmtFormula<V, F>>,
    },

    DeclareDatatypes {
        sorts: Vec<S>,
        cons: Vec<Vec<SmtCons<F>>>,
    },
    Comment(String),

    CheckSat,
    GetProof,
    SetOption(String, String),
    SetLogic(String),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtCons<F> {
    pub fun: F,
    pub dest: Vec<F>,
}

mod display;

fn fun_list_fmt<I: Iterator<Item = impl fmt::Display>>(
    f: &mut fmt::Formatter<'_>,
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


impl<'bump> Smt<'bump> {


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
        disp.propagate(self)
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
