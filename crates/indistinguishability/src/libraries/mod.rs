use egg::{Analysis, EGraph, Rewrite};
use itertools::chain;
pub use vampire::VampireRule;

use crate::libraries::base::BaseRewriteLib;
use crate::libraries::constrains::ConstrainsLib;
use crate::libraries::deduce::DeduceLib;
use crate::libraries::fa::FaLib;
use crate::libraries::find_indices::FindIndicesLib;
use crate::libraries::ifs::IfLib;
use crate::libraries::lambda::LambdaLib;
use crate::libraries::protocol::unfold::UnfoldLib;
use crate::libraries::publication::PublicationLib;
use crate::libraries::sanity_check::SanityCheck;
use crate::libraries::smt::SmtLib;
use crate::libraries::substitution::SubstLib;
use crate::libraries::utils::{EggRewriteSink, RewriteSink, RuleSink, SmtSink};
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

/// Provides rules for deduction.
mod deduce;
/// Provides rules for handling forall quantifiers.
mod fa;
/// Provides rules for lambda calculus.
mod lambda;
/// Provides rules for handling nonces.
mod nonce;
/// Provides rules for substitution.
mod substitution;
/// Provides rules for interacting with the Vampire SMT solver.
mod vampire;

mod ifs;

pub use protocol::{constrains, publication};

mod smt;

// mod is_public;

/// Simple rewrite rule to find indices
/// that can then be used with mutliparterns
mod find_indices;

pub use nonce::{FreshNonce, add_no_guessing_smt};

mod base;
mod problem;
mod protocol;

mod memory_cells;

/// Provides rules for sanity checking.
mod sanity_check;

mod library;
pub use library::Library;

#[allow(clippy::module_inception, reason = "I do what I want!")]
mod libraries;
pub use libraries::Libraries;

mod cryptography;
pub use cryptography::{AEnc, CryptographicAssumption, Cryptography, DDH, PRF, XOr};

mod current_step;

mod and_bounder;
