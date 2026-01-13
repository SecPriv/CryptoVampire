use egg::{Analysis, EGraph, Rewrite};
use itertools::chain;
/// Re-exports the test module for PRF rules.
#[cfg(test)]
pub use prf::test as prf_test;
/// Re-exports the `VampireRule` struct, which implements a rule for the Vampire SMT solver.
pub use vampire::VampireRule;

use crate::problem::{PAnalysis, PRule, ProblemState, RcRule};
use crate::runners::SmtRunner;
use crate::{Lang, MSmt, Problem};

// =========================================================
// ======================= macros ==========================
// =========================================================

/// declares variables to be used with [mk_prolog] and [mk_rewrite] and
/// derivatives.
///
/// This is just a fancy `let`.
///
/// # Example
///
/// ```
/// # use indistinguishability::{decl_vars, terms::Sort::Bitstring};
/// decl_vars!(a, b: Bitstring);
/// ```
#[macro_export]
macro_rules! decl_vars {
    ($($var:ident $(:$sort:expr)? ),+) => {
        $(
            let $var = &    $crate::fresh!($($sort)?);
        )+
    };

    ($v:vis const $(;)? $($var:ident $(:$sort:expr)? ),+ $(,)?) => {
        $($v static $var: &$crate::terms::Variable = &$crate::fresh!(const $($sort)?);)+
    };
}

/// makes a prolog rule
///
/// # Example
///
/// ```ignore
/// mk_prolog!("rule-name"; a, b: (and a b) :- (=> a b));
/// ```
macro_rules! mk_prolog {
    ($($var:ident),* $(($payload:expr))?: $pre:tt) => {
        mk_prolog!(@ false, None $(,$payload)?; ($($var),*) $pre :-)
    };
    ($name:expr; $($var:ident),* $(($payload:expr))?: $pre:tt) => {
        mk_prolog!(@ false, Some($name) $(,$payload)?; ($($var),*) $pre :-)
    };

    ($($var:ident),* $(($payload:expr))?: $pre:tt :-!, $($post:tt),*) => {
        mk_prolog!(@ true, None $(,$payload)?; ($($var),*) $pre :- $($post),*)
    };
    ($name:expr; $($var:ident),* $(($payload:expr))?: $pre:tt :-!, $($post:tt),*) => {
        mk_prolog!(@ true, Some($name) $(,$payload)?; ($($var),*) $pre :- $($post),*)
    };

    ( $($var:ident),* $(($payload:expr))?: $pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ false, None $(,$payload)?; ($($var),*) $pre :- $($post),*)
    };
    ($name:expr; $($var:ident),* $(($payload:expr))?: $pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ false, Some($name) $(,$payload)?; ($($var),*) $pre :- $($post),*)
    };


    (@ $cut:expr, $name:expr $(, $payload:expr)?; ($($var:ident),*) $pre:tt :- $($post:tt),*) => {{
        $(
            let $var = $crate::fresh!();
        )*
        ::golgge::PrologRule::builder()
            .input(egg::Pattern::from(&$crate::rexp!($pre)))
            .deps([$(egg::Pattern::from(&$crate::rexp!($post))),*])
            .maybe_name($name)
            .cut($cut)
            $(.payload($payload))?
            .build()
            .unwrap()
    }};

}

/// build many prolog rules at once
///
/// # Example
///
/// ```ignore
/// mk_many_prolog!(
///   "rule1" a, b: (and a b) :- (=> a b).
///   "rule2" a, b: (or a b) :- (=> a b).
/// );
/// ```
macro_rules! mk_many_prolog {
    (
        $(
            $name:literal  $($var:ident),* $( ($payload:expr))? :
            $pre:tt
            $(:-! $($post:tt),+)?
            $(:- $($post2:tt),+)?
        .)*
    ) => {
        vec![
            $(
                mk_prolog!($name; $($var),* $(($payload))?: $pre
                    $(:-! $($post),+)?
                    $(:- $($post2),+)?
                )
            ),*
        ]
    }
}

/// Creates a rewrite rule
///
/// # Example
///
/// ```ignore
/// mk_rewrite!("rule-name"; a, b: (and a b) => (and b a));
/// ```
macro_rules! mk_rewrite {
    (crate prolog $($name:expr;)? $(($($var:ident $sort:expr),*))?: $from:tt => $to:tt) => {{
        $($(
            let $var = $crate::fresh!($sort);
        )*)?

        $crate::terms::Rewrite::builder()
            .from($crate::rexp!($from))
            .to(mk_rewrite!(crate @@ $to))
            $(.name($name))?
            $(.variables([$($var),*]))?
            .prolog_only(true)
            .build()
    }};
    (crate $($name:expr;)? $(($($var:ident $sort:expr),*))?: $from:tt => $to:tt) => {{
        $($(
            let $var = $crate::fresh!($sort);
        )*)?

        $crate::terms::Rewrite::builder()
            .from($crate::rexp!($from))
            .to(mk_rewrite!(crate @@ $to))
            $(.name($name))?
            $(.variables([$($var),*]))?
            .build()
    }};

    (@@ (#$var:tt = #$value:tt)) => {
        ::egg::MultiPattern::new(vec![{
            let v = $var.as_egg();
            (v, $crate::terms::Formula::as_egg_var(&$crate::rexp!(#$value)))
        }])
    };

    (@@ ($(#$var:tt = $value:tt),+)) => {
        ::egg::MultiPattern::new(vec![$({
            let v = $var.as_egg();
            (v, $crate::terms::Formula::as_egg_var(&$crate::rexp!($value)))
        }),*])
    };

    (@@ (#$($value:tt)+)) => {{
        let x : $crate::terms::Formula = $crate::rexp!(#$($value)+);
        ::egg::Pattern::<$crate::Lang>::from(
            &x
        )
    }};

    (@@ $value:tt) => {
        ::egg::Pattern::from(
            &$crate::rexp!($value)
        )
    };

    (crate @@ (#$($value:tt)+)) => {{
        let x : $crate::terms::Formula = $crate::rexp!(#$($value)+);
        x
    }};

    (crate @@ $value:tt) => {
            $crate::rexp!($value)
    };

    ($name:expr; $(($($var:ident),*))?: $from:tt => $to:tt) => {{
        $($(
            let $var = $crate::fresh!();
        )*)?
        ::egg::Rewrite::new(
            $name,
            mk_rewrite!(@@ $from),
            mk_rewrite!(@@ $to),
        ).unwrap()
    }};
}

/// Creates multiple rewrite rules at once
///
/// # Example
///
/// ```ignore
/// mk_many_rewrites!(
///  ["rule1"] (and a b) => (and b a).
///  ["rule2"] (or a b) => (or b a).
/// );
/// ```
macro_rules! mk_many_rewrites {
    (
        $(
            [$name:literal]
            $from:tt => $to:tt
        .)*
    ) => {
       vec![
            $(
                mk_rewrite!($name; : $from => $to)
            ),*
        ]
    }
}

// =========================================================
// ================ modules declarations ===================
// =========================================================

// pub(crate) mod base_rules;
/// Provides utility functions and helpers for rules.
pub mod utils;

/// Encryption rules
mod aenc;

/// Provides rules for deduction.
pub mod deduce;
/// Provides default rewrite rules.
mod default_rewrites;
/// Provides rules for handling forall quantifiers.
mod fa;
/// Provides rules for lambda calculus.
mod lambda;
/// Provides rules for handling nonces.
mod nonce;
/// Provides rules for pseudo-random functions (PRFs).
mod prf;
/// Provides rules for substitution.
mod substitution;
/// Provides rules for interacting with the Vampire SMT solver.
mod vampire;

mod if_rewrites;

pub mod constrains;

mod xor;
pub use xor::XOr;

mod ddh;
pub use ddh::DDH;

mod smt;

// mod is_public;

/// Simple rewrite rule to find indices
/// that can then be used with mutliparterns
pub mod find_indices;

pub use aenc::AEnc;
pub use nonce::{FreshNonce, mk_no_guessing_smt};
/// Re-exports the `PRF` struct, representing a pseudo-random function.
pub use prf::PRF;

mod publication;

/// Provides rules for sanity checking.
#[cfg(debug_assertions)]
mod sanity_check;

// =========================================================
// ====================== exported =========================
// =========================================================

/// Creates the default prolog rules
///
/// This function creates the default prolog rules for the given problem.
/// It includes the extra rules from the problem, the deduce rules, the forall rules,
/// and the substitution rule.
/// In debug mode, it also includes the sanity check rule.
pub fn mk_golgge_rules(pbl: &Problem) -> impl Iterator<Item = RcRule> {
    let exec = SmtRunner::new(pbl);
    let vampire_rule = VampireRule::builder().exec(exec.clone()).build().into_mrc();
    let fresh_rule = FreshNonce::builder().exec(exec.clone()).build().into_mrc();
    chain![
        [
            #[cfg(debug_assertions)]
            {
                sanity_check::SanityCheck.into_mrc()
            }
        ],
        pbl.extra_rules().iter().cloned(),
        deduce::mk_rules(pbl),
        fa::mk_prolog_rules(pbl),
        [substitution::SubstRule.into_mrc(), vampire_rule, fresh_rule]
    ]
}

/// Creates the default rewrite rules
///
/// This function creates the default rewrite rules for the given problem.
/// It includes the default rewrites and the lambda rewrites.
pub fn mk_egg_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain![
        default_rewrites::mk_rewrites(pbl),
        lambda::mk_rewrites(pbl),
        if_rewrites::mk_rewrite(pbl),
        constrains::mk_rewrite(pbl),
        [find_indices::mk_rewrite()],
        publication::mk_rewrites(pbl),
    ]
}

pub fn mk_smt_prelude(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    chain![
        smt::mk_prelude(pbl),
        constrains::mk_smt(pbl),
        publication::mk_smt(pbl)
    ]
}

/// Add terms to the egraph / union terms
pub fn init_egraph<'a>(egraph: &mut EGraph<Lang, PAnalysis<'a>>) {
    constrains::modify_egraph(egraph);
    find_indices::modify_egraph(egraph);
    ProblemState::init_egraph(egraph);
}
