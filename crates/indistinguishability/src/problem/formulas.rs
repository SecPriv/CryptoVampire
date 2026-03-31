use itertools::{Itertools, chain};
use log::log_enabled;
use logic_formula::AsFormula;
use logic_formula::iterators::QuantiferIterator;
use utils::econtinue_let;

use super::cache::Context;
use super::*;
use crate::libraries::Libraries;
use crate::libraries::utils::SmtSink;
use crate::terms::{
    FOBinder, FindSuchThat, Formula, FunctionCollection, Quantifier, QuantifierT,
    QuantifierTranslator, Rewrite,
};
use crate::{MSmt, rexp};

impl Problem {
    /// Computes the SMT
    pub fn add_smt<'a>(&mut self, context: &Context, sink: &mut impl SmtSink<'a>) {
        Libraries::add_all_smt(self, context, sink);
    }

    /// Returns the extra SMT formulas
    pub fn extra_smt(&self) -> &[MSmt<'static>] {
        &self.extra_smt
    }

    /// Returns a mutable reference to the extra SMT formulas
    pub fn extra_smt_mut(&mut self) -> &mut Vec<MSmt<'static>> {
        self.cache.smt.force_reset();
        &mut self.extra_smt
    }

    /// Returns the extra rewrites
    pub fn extra_rewrite(&self) -> &[Rewrite] {
        &self.extra_rewrite
    }

    /// Returns a mutable reference to the extra rewrites
    pub fn extra_rewrite_mut(&mut self) -> &mut Vec<Rewrite> {
        self.cache.smt.force_reset();
        &mut self.extra_rewrite
    }

    /// Returns the extra rules
    pub fn extra_rules(&self) -> &[RcRule] {
        &self.extra_rules
    }

    /// Returns a mutable reference to the extra rules
    pub fn extra_rules_mut(&mut self) -> &mut Vec<RcRule> {
        &mut self.extra_rules
    }

    /// Finds all the temporary quantifiers in the problem and adds them to the cache
    pub fn find_temp_quantifiers(&mut self, extra: &[Formula]) {
        if extra.is_empty() && !self.cache.quantifier_cache.is_empty() {
            return;
        }

        tr!("looks for quantifier candidates in:");
        // unique quantifiers up to unification
        let quantifiers = {
            let candidate = chain![self.list_all_terms(), extra]
                .flat_map(|f| f.iter_with(QuantiferIterator, ()))
                .unique();
            let mut pile = Vec::new();
            for a in candidate {
                if let Formula::Quantifier {
                    head: FOBinder::FindSuchThat,
                    ..
                } = a
                    && let None = pile.iter().find_map(|x| a.unify(x))
                    && let None = self
                        .cache
                        .quantifier_cache
                        .iter()
                        .find_map(|(x, _)| a.unify(x))
                {
                    tr!("{a:?}");
                    pile.push(a.clone());
                }
            }
            pile
        };
        tr!(
            "found quantifiers!:\n{}",
            chain![
                quantifiers.iter(),
                self.cache.quantifier_cache.iter().map(|(q, _)| q)
            ]
            .join("\n")
        );

        if quantifiers.is_empty() {
            return;
        }

        tr!("generate names for quantifers");
        for q in quantifiers.iter() {
            econtinue_let!(let Formula::Quantifier { vars, arg, head: FOBinder::FindSuchThat } = q);
            let cvars = q.free_vars_iter().unique().cloned();
            let bvars = vars.iter().cloned();

            let find = FindSuchThat::insert()
                .pbl(self)
                .bvars(bvars)
                .cvars(cvars)
                .temporary(true)
                .call();
            find.set_condition(arg[0].clone());
            find.set_then_branch(arg[1].clone());
            find.set_else_branch(arg[2].clone());
            tr!("adding newfound quantifier:\n{find:#?}\n\tfrom{q}");
            let tlf = find.top_level_function().clone();
            self.cache.quantifier_cache.push((q.clone(), tlf));
        }
        self.cache.smt.force_reset();
    }

    /// Clears the temporary quantifiers from the cache
    pub fn clear_temp_quantifiers(&mut self) {
        self.cache.quantifier_cache.clear();
        self.cache.smt.force_reset();
    }

    /// list all the `RecFOFormula` stored in this `Self`
    pub fn list_all_terms(&self) -> impl Iterator<Item = &Formula> {
        chain![
            self.protocols()
                .iter()
                .flat_map(|p| p.steps().iter())
                .flat_map(|s| [&s.cond, &s.msg].into_iter()),
            self.extra_rewrite().iter().flat_map(
                |Rewrite {
                     from,
                     to,
                     prolog_only,
                     ..
                 }| {
                    (!prolog_only)
                        .then_some([from, to].into_iter())
                        .into_iter()
                        .flatten()
                }
            )
        ]
    }
}

/// This implementation allows to translate quantifiers using the cache
impl QuantifierTranslator for Problem {
    /// Attempts to translate a given quantifier formula using the cached quantifiers.
    ///
    /// Returns `Some(translated_formula)` if a translation is found, otherwise `None`.
    fn try_translate(&self, formula: &Formula) -> Option<crate::terms::Formula> {
        tr!("try translate:\n{formula}");
        if log_enabled!(log::Level::Trace) {
            let mut p = String::new();
            for (q, f) in &self.cache.quantifier_cache {
                p += &format!("{} => {q}\n", f.name);
            }
            tr!("available quantifiers:\n{p}")
        }

        let (subst, fun) = self
            .cache
            .quantifier_cache
            .iter()
            .find_map(|(cached, fun)| cached.unify(formula).map(|subst| (subst, fun.clone())))?;
        let q = fun.get_quantifier(self.functions()).unwrap();

        let Quantifier::FindSuchThat(q2) = q else {
            unreachable!()
        };
        let cond = q2.condition().unwrap();

        tr!(
            "quantifier translation:\n\tterm:\n\t{formula}\n\tfunction:{}\n\t\t(cond: \
             {cond})\n\t\tcvars:[{}],\n\tsubstitution:\n{}",
            q.top_level_function().name,
            q.cvars().iter().map(|v| format!("{v:?}")).join(", "),
            subst
                .iter()
                .map(|(v, f)| format!("\t{v:?} => {f}"))
                .join(",\n")
        );

        let args = q
            .cvars()
            .iter()
            .map(|v| subst.get(v).cloned().unwrap_or(Formula::Var(v.clone())))
            .collect_vec();
        let args = args.iter().cloned();

        tr!("arg vars: [{}]", args.clone().join(", "));

        let tlf = q.top_level_function();
        self.cache
            .smt
            .occured_quantfiers
            .borrow_mut()
            .insert(tlf.clone());

        let sks = q.skolems().iter().map(|sk| rexp!((sk #(args.clone())*)));

        Some(rexp!((tlf #(args.clone())* #sks*)))
    }
}

impl AsRef<FunctionCollection> for Problem {
    /// Returns a reference to the `FunctionCollection` within the `Problem`.
    fn as_ref(&self) -> &FunctionCollection {
        &self.function
    }
}

impl AsMut<FunctionCollection> for Problem {
    /// Returns a mutable reference to the `FunctionCollection` within the `Problem`.
    fn as_mut(&mut self) -> &mut FunctionCollection {
        &mut self.function
    }
}
