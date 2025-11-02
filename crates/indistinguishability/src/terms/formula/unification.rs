//! Substitutions for [RecFOFormula]

use std::collections::VecDeque;

use itertools::izip;
use log::trace;
use rustc_hash::FxHashMap;

use crate::terms::{RecFOFormula, Variable};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Substitution(pub FxHashMap<Variable, RecFOFormula>);

impl Substitution {
    pub fn new() -> Self {
        Self(Default::default())
    }

    /// Creates a substitution from a single binding.
    fn from_single(var: Variable, formula: RecFOFormula) -> Self {
        let mut map = FxHashMap::default();
        map.insert(var, formula);
        Self(map)
    }

    /// Applies the substitution to all *values* in `self`, then inserts the new binding.
    /// This is the core of Martelli-Montanari unification.
    pub fn add(&mut self, var: Variable, formula: RecFOFormula) {
        // Create a temporary substitution for the new binding
        let new_subst = Self::from_single(var.clone(), formula.clone());

        // Apply the new binding to all existing values in the substitution
        for value in self.0.values_mut() {
            *value = value.apply(&new_subst);
        }

        // Finally, add the new binding
        self.0.insert(var, formula);
    }
}

impl Default for Substitution {
    fn default() -> Self {
        Self::new()
    }
}

// --- Unification Error Type ---

#[derive(Debug, PartialEq, Eq)]
pub enum UnificationError {
    /// e.g., P(x) vs Q(x) or P(x) vs P(x, y)
    Mismatch,
    /// e.g., V vs P(V)
    OccursCheck,
}

// --- The MGU Function (Martelli-Montanari Algorithm) ---

pub fn mgu(f1: &RecFOFormula, f2: &RecFOFormula) -> Result<Substitution, UnificationError> {
    trace!("attempt to compute mgu of:\n\t{f1}\n\t{f2}");
    let mut equations = VecDeque::new();
    equations.push_back((f1.clone(), f2.clone()));
    let mut subst = Substitution::new();

    while let Some((t1, t2)) = equations.pop_front() {
        trace!("mgu equality for:\n\t{t1}\n\t{t2}");

        // Apply the current substitution to both terms
        let t1 = t1.apply(&subst);
        let t2 = t2.apply(&subst);

        // --- Unification Cases ---

        // 1. Identical terms: skip
        if t1 == t2 {
            continue;
        }

        // 2. Variable vs. Term
        if let RecFOFormula::Var(v) = t1 {
            unify_variable(v, t2, &mut subst, &mut equations)?;
            continue;
        }
        if let RecFOFormula::Var(v) = t2 {
            unify_variable(v, t1, &mut subst, &mut equations)?;
            continue;
        }

        // 3. App vs. App
        if let (
            RecFOFormula::App { head: h1, args: a1 },
            RecFOFormula::App { head: h2, args: a2 },
        ) = (&t1, &t2)
        {
            // Check heads and arity
            if h1 != h2 || a1.len() != a2.len() {
                return Err(UnificationError::Mismatch);
            }
            // Add all argument pairs to the equation list
            for (arg1, arg2) in a1.iter().zip(a2.iter()) {
                equations.push_back((arg1.clone(), arg2.clone()));
            }
            continue;
        }

        // 4. Quantifier vs. Quantifier (The special case)
        if let (
            RecFOFormula::Quantifier {
                head: h1,
                vars: v1,
                arg: a1,
            },
            RecFOFormula::Quantifier {
                head: h2,
                vars: v2,
                arg: a2,
            },
        ) = (&t1, &t2)
        {
            // Check binders and number of bound variables
            if h1 != h2
                || v1.len() != v2.len()
                || izip!(v1.iter(), v2.iter()).any(|(vl, vr)| vl.get_sort() != vr.get_sort())
            {
                return Err(UnificationError::Mismatch);
            }

            // --- Alpha-Renaming ---
            let mut rename_subst1 = Substitution::new();
            let mut rename_subst2 = Substitution::new();

            for (var1, var2) in v1.iter().zip(v2.iter()) {
                let fresh_var = Variable::fresh()
                    .sort(var1.get_sort().expect("bound variables must have sort"))
                    .call();
                // We don't use `add` here because these are simple, non-composing renamings
                rename_subst1
                    .0
                    .insert(var1.clone(), RecFOFormula::Var(fresh_var.clone()));
                rename_subst2
                    .0
                    .insert(var2.clone(), RecFOFormula::Var(fresh_var));
            }

            // Apply the renamings and add the new bodies to the equation list
            let new_args = izip!(a1.iter(), a2.iter())
                .map(|(a1, a2)| (a1.apply(&rename_subst1), a2.apply(&rename_subst2)));
            equations.extend(new_args);
            continue;
        }

        // 5. Any other combination is a mismatch
        // (e.g., App vs. Quantifier)
        return Err(UnificationError::Mismatch);
    }

    Ok(subst)
}

/// Helper function to handle the `Variable vs. Term` case.
fn unify_variable(
    var: Variable,
    term: RecFOFormula,
    subst: &mut Substitution,
    _equations: &mut VecDeque<(RecFOFormula, RecFOFormula)>,
) -> Result<(), UnificationError> {
    // Perform the occurs check
    if term.contains_var(&var) {
        return Err(UnificationError::OccursCheck);
    }

    // Add the new binding to the substitution.
    // `add` handles composing this new binding with the existing substitution.
    subst.add(var, term);
    Ok(())
}

// --- Unit Tests ---

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{decl_vars, rexp};

    #[test]
    fn test_quantifier_unification() {
        // --- Define some constants ---
        decl_vars!(v, z);

        // f1 = forall x. P(x, V)
        // f2 = forall y. P(y, z)
        let f1 = rexp!((forall ((#i Bool) ) (and #i #v)));
        let f2 = rexp!((forall ((#k Bool) ) (and #k #z)));

        let result = mgu(&f1, &f2);

        // We expect { V: z } or { z: V }. Our implementation will produce { V: z }
        // because (V, z) will be the equation, and unify_variable(V, z, ...) will be called.
        let mut expected_subst = Substitution::new();
        expected_subst.add(v.clone(), RecFOFormula::Var(z.clone()));

        assert_eq!(result, Ok(expected_subst));
    }

    #[test]
    fn test_quantifier_mismatch_binder() {
        decl_vars!(v, z);
        // f1 = forall x. P(x, V)
        // f2 = exists y. P(y, z)
        let f1 = rexp!((forall ((#i Bool) ) (and #i #v)));
        let f2 = rexp!((exists ((#k Bool) ) (and #k #z)));

        let result = mgu(&f1, &f2);
        assert_eq!(result, Err(UnificationError::Mismatch));
    }

    #[test]
    fn test_quantifier_mismatch_body() {
        decl_vars!(v, z);
        // f1 = forall x. P(x, V)
        // f2 = forall y. P'(y, z)
        let f1 = rexp!((forall ((#i Bool) ) (and #i #v)));
        let f2 = rexp!((forall ((#k Bool) ) (or #k #z)));

        let result = mgu(&f1, &f2);
        assert_eq!(result, Err(UnificationError::Mismatch));
    }

    #[test]
    fn test_occurs_check() {
        decl_vars!(v);
        // f1 = forall x. P(x, V)
        let f1 = rexp!((forall ((#i Bool) ) (and #i #v)));
        // f_v = V
        let f_v = RecFOFormula::Var(v.clone());

        let result = mgu(&f_v, &f1);
        assert_eq!(result, Err(UnificationError::OccursCheck));
    }

    #[test]
    fn test_standard_substitution() {
        decl_vars!(v, w);
        // f1 = forall x. P(x, V)
        let f1 = rexp!((forall ((#i Bool) ) (and #i #v)));
        // f_v = V
        let f_w = RecFOFormula::Var(w.clone());

        let result = mgu(&f_w, &f1);

        let mut expected_subst = Substitution::new();
        expected_subst.add(w.clone(), f1); // Expect { W: forall x. P(x, V) }

        assert_eq!(result, Ok(expected_subst));
    }
}
