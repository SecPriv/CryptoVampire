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
            let $var = $crate::fresh!($($sort)?);
        )+
    };

    (const $(;)? $($var:ident $(:$sort:expr)? ),+ $(,)?) => {
        $(static $var: $crate::terms::Variable = $crate::fresh!(const $($sort)?);)+
    };
}

/// makes prolog rules
///
/// ```text
/// mk_prolog!("hey"; (and #0 #1) :- (=> #0 #1))
/// ```
macro_rules! mk_prolog {
    ($($var:ident),*: $pre:tt) => {
        mk_prolog!(@ None; ($($var),*) $pre :-)
    };
    ($name:expr; $($var:ident),*: $pre:tt) => {
        mk_prolog!(@ Some($name); ($($var),*) $pre :-)
    };
    ($($var:ident),*: $pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ None; ($($var),*) $pre :- $($post),*)
    };
    ($name:expr; $($var:ident),*: $pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ Some($name); ($($var),*) $pre :- $($post),*)
    };


    (@ $name:expr; ($($var:ident),*) $pre:tt :- $($post:tt),*) => {{
        $(
            let $var = $crate::fresh!();
        )*
        ::golgge::PrologRule::builder()
            .input(egg::Pattern::from(&$crate::rexp!($pre)))
            .deps([$(egg::Pattern::from(&$crate::rexp!($post))),*])
            .maybe_name($name)
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
            $(:- $($post:tt),+)?
        .)*
    ) => {
        vec![
            $(
                mk_prolog!($name; $($var),*: $pre $(:- $($post),+)? )
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
            let v = ::egg::Var::from($var);
            (v, $crate::rexp!(#$value).as_egg_var())
        }])
    };

    (@@ ($(#$var:tt = $value:tt),+)) => {
        ::egg::MultiPattern::new(vec![$({
            let v = ::egg::Var::from($var);
            (v, $crate::rexp!($value).as_egg_var())
        }),*])
    };

    (@@ (#$($value:tt)+)) => {
        ::egg::Pattern::from(
            &$crate::rexp!(#$($value)+)
        )
    };

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

pub use nonce::{FreshNonce, mk_no_guessing_smt};
pub use prf::PRF;

#[cfg(debug_assertions)]
mod sanity_check;

// ~~~~~~~~~~~~~~~ helpers ~~~~~~~~~~~~~~~~~~

fn var_as_recexpr<'a, L>(vars: implvec!(&'a egg::Var)) -> Vec<[ENodeOrVar<L>; 1]> {
    vars.into_iter()
        .copied()
        .map(ENodeOrVar::Var)
        .map(|x| [x])
        .collect()
}

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
        [substitution::SubstRule.into_mrc()]
    ]
}

pub fn mk_default_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain![default_rewrites::mk_rewrites(pbl), lambda::mk_rewrites(pbl)]
}
