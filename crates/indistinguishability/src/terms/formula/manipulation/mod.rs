use rpds::HashTrieSet;
use rustc_hash::FxHashMap;

use super::Formula;
use crate::terms::Variable;

mod unification;
pub use unification::Substitution;

// =========================================================
// ==================== manipulation =======================
// =========================================================
// substitution, unification, etc...

#[non_exhaustive]
#[derive(Debug)]
pub struct AlphaArgs<'var, 'r> {
    pub var: &'var Variable,
    pub subst: &'r mut FxHashMap<&'var Variable, Variable>,
}

impl Formula {
    // ~~~~~~~~~~~~ alpha renaming ~~~~~~~~~~~~~~

    /// Renames the variables in `self` that verify `do_change` with fresh ones.
    /// It populate `subst` as it goes with the substitution it creates. If a
    /// substution was alreay there, it extends it.
    ///
    /// ## Notes
    /// - `do_change` has priority over the pre-existing substitution to
    ///   decide how to modify the variables
    /// - it effectively clones `self`.
    pub fn alpha_rename_if_with<'a>(
        &'a self,
        subst: &mut FxHashMap<&'a Variable, Variable>,
        do_change: &mut impl FnMut(AlphaArgs<'a, '_>) -> bool,
    ) -> Self {
        match self {
            Self::App { head, args } => Self::App {
                head: head.clone(),
                args: args
                    .iter()
                    .map(|arg| arg.alpha_rename_if_with(subst, do_change))
                    .collect(),
            },
            Self::Var(var) => {
                if do_change(AlphaArgs { var, subst }) {
                    Self::Var(
                        subst
                            .entry(var)
                            .or_insert_with(|| Variable::fresh().maybe_sort(var.get_sort()).call())
                            .clone(),
                    )
                } else {
                    self.clone()
                }
            }
            Self::Quantifier { head, vars, arg } => {
                let head = *head;
                let vars = vars
                    .iter()
                    .map(|var| {
                        if do_change(AlphaArgs { var, subst }) {
                            subst
                                .entry(var)
                                .or_insert_with(|| {
                                    Variable::fresh().maybe_sort(var.get_sort()).call()
                                })
                                .clone()
                        } else {
                            var.clone()
                        }
                    })
                    .collect();
                let arg = arg
                    .iter()
                    .map(|arg| arg.alpha_rename_if_with(subst, do_change))
                    .collect();
                Self::Quantifier { head, vars, arg }
            }
        }
    }

    /// Freshen all the variables to ensure their uniqueness
    ///
    /// ## arguments
    /// - `predicate`: a function that return `true` if the variable must be
    ///   renamed
    pub fn alpha_rename_if(&self, mut do_change: impl FnMut(&Variable) -> bool) -> Self {
        self.alpha_rename_if_with(
            &mut FxHashMap::default(),
            &mut |AlphaArgs { var, .. }| do_change(var),
        )
    }

    /// Make all the variables apearing in `self` unique to `self`
    pub fn alpha_rename(&self) -> Self {
        self.alpha_rename_if_with(&mut FxHashMap::default(), &mut |_| true)
    }

    /// Apply a specific variable substitution
    pub fn apply_substitution<'a>(&'a self, subst: &mut FxHashMap<&'a Variable, Variable>) -> Self {
        self.alpha_rename_if_with(subst, &mut |AlphaArgs { var, subst }| {
            subst.contains_key(var)
        })
    }

    // ~~~~~~~~~~~~~ unification ~~~~~~~~~~~~~~~~
    pub fn unify(&self, other: &Self) -> Option<FxHashMap<Variable, Self>> {
        match unification::mgu(self, other) {
            Ok(Substitution(map)) => Some(map),
            Err(_) => None,
        }
    }

    /// capture avoiding substitution
    pub fn subst(&self, subst: &[(Variable, Self)]) -> Self {
        self.inner_subst(subst, &Default::default())
    }

    /// helper function for [Self::subst]
    fn inner_subst(&self, subst: &[(Variable, Self)], bvars: &HashTrieSet<Variable>) -> Self {
        match self {
            Self::Quantifier { head, vars, arg } => {
                let mut bvars = bvars.clone();
                for v in vars.iter() {
                    bvars.insert_mut(v.clone());
                }
                Self::Quantifier {
                    head: *head,
                    vars: vars.clone(),
                    arg: arg
                        .iter()
                        .map(|arg| arg.inner_subst(subst, &bvars))
                        .collect(),
                }
            }
            Self::App { head, args } => Self::App {
                head: head.clone(),
                args: args.iter().map(|x| x.inner_subst(subst, bvars)).collect(),
            },
            Self::Var(var) => if !bvars.contains(var)
                && let Some((_, expr)) = subst.iter().find(|(v, _)| v == var)
            {
                expr
            } else {
                self
            }
            .clone(),
        }
    }

    // new attemp

    /// Recursively applies a substitution to a formula.
    pub fn apply(&self, subst: &Substitution) -> Self {
        match self {
            // If we are a variable, check if we are in the substitution
            Formula::Var(v) => subst.0.get(v).cloned().unwrap_or_else(|| self.clone()),

            // For an application, apply to all arguments
            Formula::App { head, args } => Formula::App {
                head: head.clone(),
                args: args.iter().map(|arg| arg.apply(subst)).collect(),
            },

            // For a quantifier, we must apply the substitution *without*
            // touching variables that are shadowed by the quantifier's binders.
            Formula::Quantifier { head, vars, arg } => {
                // 1. Clone the substitution
                let mut shadowed_subst = subst.clone();

                // 2. Remove any bindings for variables that are now bound
                for v in vars.iter() {
                    shadowed_subst.0.remove(v);
                }

                // 3. Apply the filtered substitution to the body
                Formula::Quantifier {
                    head: *head,
                    vars: vars.clone(),
                    arg: arg.iter().map(|x| x.apply(&shadowed_subst)).collect(),
                }
            }
        }
    }

    /// Checks if a variable occurs *free* within a formula.
    /// This is the "occurs check".
    pub fn contains_var(&self, var: &Variable) -> bool {
        match self {
            Formula::Var(v) => v == var,
            Formula::App { args, .. } => args.iter().any(|arg| arg.contains_var(var)),
            Formula::Quantifier { vars, arg, .. } => {
                // If the variable is bound by *this* quantifier, it does
                // not count as a free occurrence.
                if vars.iter().any(|v| v == var) {
                    false
                } else {
                    // Otherwise, check the body.
                    arg.iter().any(|arg| arg.contains_var(var))
                }
            }
        }
    }
}
