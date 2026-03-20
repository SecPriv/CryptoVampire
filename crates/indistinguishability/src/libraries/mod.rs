use cryptovampire_smt::SmtSink;
use egg::{Analysis, EGraph, Rewrite};
use itertools::chain;
/// Re-exports the test module for PRF rules.
#[cfg(test)]
pub use prf::test as prf_test;
/// Re-exports the `VampireRule` struct, which implements a rule for the Vampire SMT solver.
pub use vampire::VampireRule;

use crate::libraries::find_indices::FindIndicesLib;
use crate::libraries::sanity_check::SanityCheck;
use crate::libraries::utils::{RewriteSink, RuleSink, EggRewriteSink};
use crate::libraries::vampire::VampireLib;
use crate::problem::{PAnalysis, PRule, ProblemState, RcRule};
use crate::runners::SmtRunner;
use crate::{CVProgram, Lang, MSmt, MSmtParam, Problem};

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

mod ifs;

pub use protocol::{constrains, publication};

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
pub use nonce::{FreshNonce, add_no_guessing_smt};
/// Re-exports the `PRF` struct, representing a pseudo-random function.
pub use prf::PRF;

mod base;
mod problem;
mod protocol;

mod memory_cells;

/// Provides rules for sanity checking.
#[cfg(debug_assertions)]
mod sanity_check;

mod library;
pub use library::Library;

// =========================================================
// ====================== exported =========================
// =========================================================

macro_rules! mk_libraires {
  ($vis:vis $name:ident; $($libs:ident),*) => {

    $vis struct $name;

    impl Library for $name {
        fn add_static_smt(pbl: &mut Problem, sink: &mut impl SmtSink<MSmtParam>) {
          $($libs::add_static_smt(pbl, sink));*
        }

        fn add_dynamic_smt(pbl: &mut Problem, sink: &mut impl SmtSink<MSmtParam>) {
          $($libs::add_dynamic_smt(pbl, sink));*
        }

        fn add_static_rewrites(pbl: &mut Problem, sink: &mut impl RewriteSink) {
          $($libs::add_static_rewrites(pbl, sink));*
        }

        fn add_dynamic_rewrites(pbl: &mut Problem, sink: &mut impl RewriteSink) {
          $($libs::add_dynamic_rewrites(pbl, sink));*
        }

        fn add_static_egg_rewrites<N:Analysis<Lang>>(pbl: &mut Problem, sink: &mut impl EggRewriteSink<N>) {
          $($libs::add_static_egg_rewrites(pbl, sink));*
        }

        fn add_dynamic_egg_rewrites<N:Analysis<Lang>>(pbl: &mut Problem, sink: &mut impl EggRewriteSink<N>) {
          $($libs::add_dynamic_egg_rewrites(pbl, sink));*
        }

        fn add_static_rules(pbl: &mut Problem, sink: &mut impl RuleSink) {
          $($libs::add_static_rules(pbl, sink));*
        }

        fn add_dynamic_rules(pbl: &mut Problem, sink: &mut impl RuleSink) {
          $($libs::add_dynamic_rules(pbl, sink));*
        }

        fn init_egraph<'a>(egraph: &mut EGraph<Lang, PAnalysis<'a>>) {
          $($libs::init_egraph(egraph));*
        }
    }
  };
}

mk_libraires!(pub Libraries; VampireLib, SanityCheck, ProblemState, ProblemState, FindIndicesLib);

/// Creates the default prolog rules
///
/// This function creates the default prolog rules for the given problem.
/// It includes the extra rules from the problem, the deduce rules, the forall rules,
/// and the substitution rule.
/// In debug mode, it also includes the sanity check rule.
pub fn add_golgge_rules(pbl: &mut Problem, sink: &mut impl utils::RuleSink) {
    Libraries::add_static_rules(pbl, sink);
    Libraries::add_dynamic_rules(pbl, sink);


    deduce::add_rules(pbl, sink);
    fa::add_prolog_rules(pbl, sink);
    sink.add_rule(substitution::SubstRule);
}

/// Creates the default rewrite rules
///
/// This function creates the default rewrite rules for the given problem.
/// It includes the default rewrites and the lambda rewrites.
pub fn add_egg_rewrites<N: Analysis<Lang>>(
    pbl: &mut Problem,
    sink: &mut impl utils::EggRewriteSink<N>,
) {
    Libraries::add_all_egg_rewrites(pbl, sink);

    base::add_rewrites(pbl, sink);
    protocol::unfold::add_rewrites(pbl, sink);
    lambda::add_rewrites(pbl, sink);
    ifs::add_rewrites(pbl, sink);
    constrains::add_rewrites(pbl, sink);
    publication::add_rewrites(pbl, sink);
}

pub fn mk_smt_prelude(pbl: &mut Problem, sink: &mut impl SmtSink<MSmtParam>) {
    Libraries::add_all_smt(pbl, sink);

    smt::add_prelude(pbl, sink);
    constrains::add_smt(pbl, sink);
    publication::add_smt(pbl, sink);
}

/// Add terms to the egraph / union terms
pub fn init_egraph<'a>(egraph: &mut EGraph<Lang, PAnalysis<'a>>) {
    Libraries::init_egraph(egraph);

    constrains::modify_egraph(egraph);
}

impl Libraries {
    pub fn recompute_egg_rewrite_rules<'a>(prgm: &mut CVProgram<'a>) {
        let mut eq_rules = prgm.take_eq_rules();
        // TODO: replace by `Libraries::add_all_egg_rewrites(pbl, sink);` once everything got inlined
        add_egg_rewrites(prgm.egraph_mut().analysis.pbl_mut(), &mut eq_rules);

        prgm.set_eq_rules(eq_rules);
    }
}