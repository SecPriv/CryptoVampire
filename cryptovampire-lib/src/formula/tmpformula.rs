use std::fmt::Display;

use anyhow::{anyhow, bail};
use log::{debug, trace, warn};
use utils::{implvec, string_ref::StrRef};

use crate::{
    environement::traits::Realm,
    formula::{
        formula::RichFormula,
        function::{signature::Signature, Function},
        quantifier::Quantifier,
        sort::{builtins::BOOL, sort_proxy::SortProxy},
        variable::{uvar, Variable},
    },
};
use hashbrown::HashMap;
use itertools::Itertools;

/// A very simplified AST
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TmpFormula {
    Binder {
        head: String,
        vars: Vec<String>,
        args: Vec<TmpFormula>,
    },
    App {
        head: String,
        args: Vec<TmpFormula>,
    },
    Var(String),
}

impl TmpFormula {
    pub fn new(head: String, args: implvec!(TmpFormula)) -> Self {
        Self::App {
            head,
            args: args.into_iter().collect(),
        }
    }

    pub fn new_const(head: String) -> Self {
        Self::App { head, args: vec![] }
    }
    pub fn new_from_ref(head: &str, args: &[TmpFormula]) -> Self {
        Self::new(head.to_string(), args.to_vec())
    }

    pub fn head(&self) -> Option<&str> {
        match self {
            Self::App { head, .. } | Self::Binder { head, .. } => Some(head),

            _ => None,
        }
    }

    pub fn args(&self) -> Option<&[TmpFormula]> {
        match self {
            Self::App { args, .. } | Self::Binder { args, .. } => Some(args.as_ref()),
            _ => None,
        }
    }

    /// Convert to a [RichFormula].
    ///
    /// - `function` the map of known function
    /// - `variable` the currenlty assigned variables (you should start with [Default::default])
    /// - `expected_sort` the expected sort. See [SortProxy] for more informations
    ///
    /// The function will try to infer the sort on its own. If it gets something
    /// it doesn't know, it turns it into a [Variable] and will consistently do so
    /// for all other instance, it will also try to match the chosen variables.
    ///
    /// Overall, it returns a [RichFormula] that unifies with the "currect" one.
    pub fn to_rich_formula<'a, 'bump>(
        &'a self,
        functions: &HashMap<StrRef<'bump>, Function<'bump>>,
        expected_sort: SortProxy<'bump>,
        variables: &mut VarHashMap<'a, 'bump>,
    ) -> anyhow::Result<RichFormula<'bump>> {
        trace!("to_rich_formula({self}, {expected_sort})");
        let realm = &Realm::Evaluated;

        match self {
            TmpFormula::App { head, args } => {
                self.convert_app(functions, expected_sort, variables, realm, head, args)
            }
            TmpFormula::Binder { head, vars, args } => {
                self.convert_binder(functions, expected_sort, variables, realm, head, vars, args)
            }
            TmpFormula::Var(_) => self.convert_variable(variables, expected_sort, realm),
        }
    }

    fn convert_app<'a, 'bump>(
        &'a self,
        functions: &HashMap<StrRef<'bump>, Function<'bump>>,
        expected_sort: SortProxy<'bump>,
        variables: &mut VarHashMap<'a, 'bump>,
        realm: &Realm,
        head: &'a str,
        args: &'a [TmpFormula],
    ) -> Result<RichFormula<'bump>, anyhow::Error> {
        if let Some(f) = functions.get(head) {
            if f.is_tmp() {
                debug!("failed: tmp function\n\t=>{self}");
                bail!("tmp function")
            }
            let sign = f.signature();
            trace!("{:?} : {sign:?}", f.as_inner());
            sign.out().unify(&expected_sort, realm).map_err(|_| {
                warn!("failed: inference error\n\t=>{self}\n{realm}\n{expected_sort}");
                anyhow!("infernce error")
            })?;
            let mut rf_args = vec![];
            for e in args.iter().zip_longest(sign.args()) {
                match e {
                    itertools::EitherOrBoth::Left(_) => {
                        debug!("failed: more arguments that expected\n\t=>{self}");
                        bail!("more arguments that expected in {:}", &self)
                    }
                    itertools::EitherOrBoth::Right(_) => break,
                    itertools::EitherOrBoth::Both(arg, sort) => {
                        rf_args.push(arg.to_rich_formula(functions, sort, variables)?.into_arc())
                    }
                }
            }
            Ok(RichFormula::Fun(*f, rf_args.into()))
        } else {
            self.convert_variable(variables, expected_sort, realm)
        }
    }

    fn convert_binder<'a, 'bump>(
        &'a self,
        functions: &HashMap<StrRef<'bump>, Function<'bump>>,
        expected_sort: SortProxy<'bump>,
        variables: &mut VarHashMap<'a, 'bump>,
        realm: &Realm,
        head: &'a str,
        vars: &'a [String],
        args: &'a [TmpFormula],
    ) -> Result<RichFormula<'bump>, anyhow::Error> {
        // TODO: include more quantifiers
        expected_sort
            .unify(&BOOL.clone().into(), realm)
            .map_err(|_| anyhow!("quantifier are booleans, expected {expected_sort} in {self}"))?;
        // check that we expect a bool
        let vars: Result<Vec<_>, _> = vars // gather the vars
            .iter()
            .map(|v| {
                TmpOrStr::from(v.as_str()).to_rich_formula_variable(
                    variables,
                    Default::default(),
                    realm,
                )
            })
            .collect();
        let vars = vars?.into();
        // turn the Vec into a Arc<[]>
        let binder = match head {
            // get the binder
            "exists" => Quantifier::Exists { variables: vars },
            "forall" => Quantifier::Forall { variables: vars },
            _ => bail!("unsopperted quantifier in {self}"),
        };
        let arg = match args {
            // get the arg
            [arg] => {
                let mut variables = variables.clone();
                /* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                since we have new scoped variables, things might get unsound
                if we don't copy. Consider the case of (forall i. sk(i)) /\ (exists i. sk(i)).
                Both `sk(i)` shouldn't be turned into the same variables.
                */
                arg.to_rich_formula(functions, BOOL.clone().into(), &mut variables)?
            }
            _ => bail!("no enough of too many arguments in {self}"),
        };
        Ok(RichFormula::Quantifier(binder, arg.into()))
    }

    pub fn as_tmp_or_str(&'_ self) -> TmpOrStr<'_> {
        self.into()
    }

    /// turn `self` into a [RichFormula::Var]
    fn convert_variable<'a, 'bump>(
        &'a self,
        variables: &mut VarHashMap<'a, 'bump>,
        expected_sort: SortProxy<'bump>,
        realm: &Realm,
    ) -> Result<RichFormula<'bump>, anyhow::Error> {
        Ok(RichFormula::Var(
            TmpOrStr::from(self).to_rich_formula_variable(variables, expected_sort, realm)?,
        ))
    }
}

impl Display for TmpFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TmpFormula::App { head, args } => {
                write!(f, "{:}(", &head)?;
                for arg in args {
                    write!(f, "{:}, ", arg)?;
                }
                write!(f, ")")
            }
            TmpFormula::Binder { head, vars, args } => {
                write!(f, "{:}(", &head)?;
                for var in vars {
                    write!(f, "{:}, ", var)?;
                }
                write!(f, ") {{")?;
                for arg in args {
                    write!(f, "{:}; ", arg)?;
                }
                write!(f, "}}")
            }
            TmpFormula::Var(s) => s.fmt(f),
        }
    }
}

/// shortcut type name, in case we change it later
pub type VarHashMap<'a, 'bump> = HashMap<TmpOrStr<'a>, Variable<'bump>>;
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum TmpOrStr<'a> {
    TmpFormula(&'a TmpFormula),
    Str(&'a str),
}

impl<'a> TmpOrStr<'a> {
    /// turn `self` into a [Variable]
    fn to_rich_formula_variable<'bump>(
        self,
        variables: &mut VarHashMap<'a, 'bump>,
        expected_sort: SortProxy<'bump>,
        realm: &Realm,
    ) -> Result<Variable<'bump>, anyhow::Error> {
        let v = if let Some(&v) = variables
            .get(&self)
            .and_then(|v| expected_sort.expects(*v.sort(), realm).ok().map(|_| v))
        {
            v
        } else if let Some(s) = expected_sort.as_option() {
            let i: uvar = variables.len().try_into().unwrap();

            // i is fresh
            debug_assert!(variables.values().map(|v| v.id()).all(|j| i != j));

            let v = Variable::new(i, s);
            variables.insert(self, v);
            v //Ok(RichFormula::Var(v))
        } else {
            debug!("failed: infernce error\n\t=>{self}");
            bail!("inference error")
        };
        Ok(v)
    }
}

impl<'a> From<&'a str> for TmpOrStr<'a> {
    fn from(v: &'a str) -> Self {
        Self::Str(v)
    }
}

impl<'a> From<&'a TmpFormula> for TmpOrStr<'a> {
    fn from(v: &'a TmpFormula) -> Self {
        Self::TmpFormula(v)
    }
}

impl<'a> std::fmt::Display for TmpOrStr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TmpOrStr::TmpFormula(tmp) => tmp.fmt(f),
            TmpOrStr::Str(s) => s.fmt(f),
        }
    }
}
