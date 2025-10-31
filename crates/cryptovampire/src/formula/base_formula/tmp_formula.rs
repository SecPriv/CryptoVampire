use hashbrown::HashMap;
use itertools::Itertools;
use log::{debug, trace};
use utils::string_ref::StrRef;

use super::BaseFormula;
use crate::environement::traits::Realm;
use crate::error::CVContext;
use crate::formula::formula::RichFormula;
use crate::formula::function::Function;
use crate::formula::function::signature::Signature;
use crate::formula::quantifier::Quantifier;
use crate::formula::sort::builtins::BOOL;
use crate::formula::sort::sort_proxy::{InferenceError, SortProxy};
use crate::formula::variable::{Variable, uvar};
use crate::{bail_at, error_at};

pub type TmpFormula = BaseFormula<String, String, String>;

impl TmpFormula {
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
    ) -> crate::Result<RichFormula<'bump>> {
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
    ) -> crate::Result<RichFormula<'bump>> {
        if let Some(f) = functions.get(head) {
            if f.is_tmp() {
                debug!("failed: tmp function\n\t=>{self}");
                bail_at!(self, "tmp function")
            }
            let sign = f.signature();
            trace!("{:?} : {sign:?}", f.as_inner());
            sign.out().unify(&expected_sort, realm)?;
            let mut rf_args = vec![];
            for e in args.iter().zip_longest(sign.args()) {
                match e {
                    itertools::EitherOrBoth::Left(_) => {
                        debug!("failed: more arguments that expected\n\t=>{self}");
                        bail_at!(self, "more arguments that expected")
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

    #[allow(clippy::too_many_arguments)]
    fn convert_binder<'a, 'bump>(
        &'a self,
        functions: &HashMap<StrRef<'bump>, Function<'bump>>,
        expected_sort: SortProxy<'bump>,
        variables: &mut VarHashMap<'a, 'bump>,
        realm: &Realm,
        head: &'a str,
        vars: &'a [String],
        args: &'a [TmpFormula],
    ) -> crate::Result<RichFormula<'bump>> {
        // TODO: include more quantifiers
        expected_sort
            .unify(&(*BOOL).into(), realm)
            .map_err(|_| error_at!(self, "quantifier are booleans, expected {expected_sort}"))?;
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
            _ => bail_at!(self, "unsopperted quantifier"),
        };
        let arg = match args {
            // get the arg
            [arg] => {
                let mut variables = variables.clone();
                // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                // since we have new scoped variables, things might get unsound
                // if we don't copy. Consider the case of (forall i. sk(i)) /\ (exists i. sk(i)).
                // Both `sk(i)` shouldn't be turned into the same variables.
                arg.to_rich_formula(functions, (*BOOL).into(), &mut variables)?
            }
            _ => bail_at!(self, "no enough of too many arguments"),
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
    ) -> crate::Result<RichFormula<'bump>> {
        Ok(RichFormula::Var(
            TmpOrStr::from(self).to_rich_formula_variable(variables, expected_sort, realm)?,
        ))
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
    ) -> crate::Result<Variable<'bump>> {
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
            return InferenceError::cant_infer(&expected_sort).with_pre_location(&(), &self);
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
