use ::utils::implvec;
use egg::{Analysis, ENodeOrVar, Rewrite};
use itertools::chain;
#[cfg(test)]
pub use prf::test as prf_test;
pub use vampire::VampireRule;

use crate::problem::{PRule, RcRule};
use crate::{Lang, Problem};

// =========================================================
// ======================= macros ==========================
// =========================================================

/// declares variables to be used with [mk_prolog] and [mk_rewrite] and
/// derivatives.
///
/// This is just a fancy `let`.
#[macro_export]
macro_rules! decl_vars {
    ($($var:ident $(:$sort:expr)? ),+) => {
        $(
            let $var = &    $crate::fresh!($($sort)?);
        )+
    };

    (const $(;)? $($var:ident $(:$sort:expr)? ),+ $(,)?) => {
        $(static $var: &$crate::terms::Variable = &$crate::fresh!(const $($sort)?);)+
    };
}

/// makes prolog rules
///
/// ```text
/// mk_prolog!("hey"; (and #0 #1) :- (=> #0 #1))
/// ```
macro_rules! mk_prolog {
    ($($var:ident),*: $pre:tt) => {
        mk_prolog!(@ false, None; ($($var),*) $pre :-)
    };
    ($name:expr; $($var:ident),*: $pre:tt) => {
        mk_prolog!(@ false, Some($name); ($($var),*) $pre :-)
    };

    ($($var:ident),*: $pre:tt :-!, $($post:tt),*) => {
        mk_prolog!(@ true, None; ($($var),*) $pre :- $($post),*)
    };
    ($name:expr; $($var:ident),*: $pre:tt :-!, $($post:tt),*) => {
        mk_prolog!(@ true, Some($name); ($($var),*) $pre :- $($post),*)
    };

    ($($var:ident),*: $pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ false, None; ($($var),*) $pre :- $($post),*)
    };
    ($name:expr; $($var:ident),*: $pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ false, Some($name); ($($var),*) $pre :- $($post),*)
    };


    (@ $cut:expr, $name:expr; ($($var:ident),*) $pre:tt :- $($post:tt),*) => {{
        $(
            let $var = $crate::fresh!();
        )*
        ::golgge::PrologRule::builder()
            .input(egg::Pattern::from(&$crate::rexp!($pre)))
            .deps([$(egg::Pattern::from(&$crate::rexp!($post))),*])
            .maybe_name($name)
            .cut($cut)
            .build()
            .unwrap()
    }};
}

/// build many prolog rules at once
macro_rules! mk_many_prolog {
    (
        $(
            $name:literal $($var:ident),* :
            $pre:tt
            $(:-! $($post:tt),+)?
            $(:- $($post2:tt),+)?
        .)*
    ) => {
        vec![
            $(
                mk_prolog!($name; $($var),*: $pre
                    $(:-! $($post),+)?
                    $(:- $($post2),+)?
                )
            ),*
        ]
    }
}

macro_rules! mk_rewrite {
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

    (@@ (#$var:tt = #$value:tt)) => {
        ::egg::MultiPattern::new(vec![{
            let v = $var.as_egg();
            (v, $crate::terms::RecFOFormula::as_egg_var(&$crate::rexp!(#$value)))
        }])
    };

    (@@ ($(#$var:tt = $value:tt),+)) => {
        ::egg::MultiPattern::new(vec![$({
            let v = $var.as_egg();
            (v, $crate::terms::RecFOFormula::as_egg_var(&$crate::rexp!($value)))
        }),*])
    };

    (@@ (#$($value:tt)+)) => {{
        let x : $crate::terms::RecFOFormula = $crate::rexp!(#$($value)+);
        ::egg::Pattern::<$crate::Lang>::from(
            &x
        )
    }};

    (@@ $value:tt) => {
        ::egg::Pattern::from(
            &$crate::rexp!($value)
        )
    };
}

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
pub mod utils;

mod deduce;
mod default_rewrites;
mod lambda;
mod nonce;
mod prf;
mod substitution;
mod vampire;
mod fa;

pub use nonce::{FreshNonce, mk_no_guessing_smt};
pub use prf::PRF;

#[cfg(debug_assertions)]
mod sanity_check;

// =========================================================
// ====================== exported =========================
// =========================================================

pub fn mk_default_prolog_rules(pbl: &Problem) -> impl Iterator<Item = RcRule> {
    chain![
        [
            #[cfg(debug_assertions)]
            {
                sanity_check::SanityCheck.into_mrc()
            }
        ],
        pbl.extra_rules().iter().cloned(),
        deduce::mk_rules(pbl),
        fa::mk_rules(pbl),
        [substitution::SubstRule.into_mrc()]
    ]
}

pub fn mk_default_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain![default_rewrites::mk_rewrites(pbl), lambda::mk_rewrites(pbl)]
}
