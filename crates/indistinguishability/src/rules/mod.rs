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
macro_rules! decl_vars {
    ($($var:ident),+) => {
        let [$($var),+] =
            ::std::array::from_fn(|i| ::egg::Var::from_u32(i as u32))
                .map(::egg::ENodeOrVar::Var::<$crate::Lang>);
    };

    ($N:ident:$t:ty; $($var:ident),+) => {
        decl_vars![$($var),+];
        static $N: $t = decl_vars!(@ $($var)+) + 1;
    };

    ($N:ident; $($var:ident),+) => {
        decl_vars!($N:u32; $($var),*)
    };

    (@ $t:tt) => {
        1
    };

    (@ $t:tt $($o:tt)+) => {
        1 + decl_vars!(@ $($o)+)
    }
}

/// makes prolog rules
///
/// ```text
/// mk_prolog!("hey"; (and #0 #1) :- (=> #0 #1))
/// ```
macro_rules! mk_prolog {
    ($pre:tt) => {
        mk_prolog!(@ None; $pre :-)
    };
    ($name:expr; $pre:tt) => {
        mk_prolog!(@ Some($name); $pre :-)
    };
    ($pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ None; $pre :- $($post),*)
    };
    ($name:expr; $pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ Some($name); $pre :- $($post),*)
    };

    (@ $name:expr; $pre:tt :- $($post:tt),*) => {
        ::golgge::PrologRule::builder()
            .input($crate::rexp!($pre).into_iter().collect())
            .deps([$($crate::rexp!($post).into_iter().collect()),*])
            .maybe_name($name)
            .build()
            .unwrap()
    };
}

/// build many prolog rules at once
macro_rules! mk_many_prolog {
    (
        $(
            [$name:literal]
            $pre:tt
            $(:- $($post:tt),+)?
        .)*
    ) => {
        vec![
            $(
                mk_prolog!($name; $pre $(:- $($post),+)? )
            ),*
        ]
    }
}

macro_rules! mk_rewrite {
    ($name:expr; $from:tt => $to:tt) => {
        ::egg::Rewrite::new(
            $name,
            mk_rewrite!(@@ $from),
            mk_rewrite!(@@ $to),
        ).unwrap()
    };

    (@@ (#$var:tt = #$value:tt)) => {
        ::egg::MultiPattern::new(vec![{
            let [::egg::ENodeOrVar::Var(v)] = $crate::rexp!(#$var) else {
                panic!("left side of `=` should be a variable")
            };
            (v, $crate::rexp!(#$value).into_iter().collect())
        }])
    };

    (@@ ($(#$var:tt = $value:tt),+)) => {
        ::egg::MultiPattern::new(vec![$({
            let [::egg::ENodeOrVar::Var(v)] = $crate::rexp!(#$var) else {
                panic!("left side of `=` should be a variable")
            };
            (v, $crate::rexp!($value).into_iter().collect())
        }),*])
    };

    (@@ (#$($value:tt)+)) => {
        ::egg::Pattern::from_iter(
            $crate::rexp!(#$($value)+)
        )
    };

    (@@ $value:tt) => {
        ::egg::Pattern::from_iter(
            $crate::rexp!($value)
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
                mk_rewrite!($name; $from => $to)
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
        deduce::mk_rules(pbl).map(|x| x.into_mrc()),
        [substitution::SubstRule.into_mrc()]
    ]
}

pub fn mk_default_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain![default_rewrites::mk_rewrites(pbl), lambda::mk_rewrites(pbl)]
}
