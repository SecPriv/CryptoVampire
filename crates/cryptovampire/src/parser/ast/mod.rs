//! This module tries to build an [AST](https://en.wikipedia.org/wiki/Abstract_syntax_tree)
//! for a `cryptovampire` file. It is just a representation of the file with *no* processing
//! applied to it (e.g., no type checking, macro unfolding,...). See the [super::parser] module
//! to see the processing take place.

// This files
//  - builds useful macros
//  - defines a bunch of re-exported module for each sub-ASTs

use std::fmt::Display;
use std::slice::{self, Iter};
use std::sync::Arc;

use derivative::Derivative;
use itertools::{Itertools, chain};
use log::trace;
use pest::Parser;
use pest::iterators::Pair;
use utils::vecref::VecRef;
use utils::{destvec, implvec, match_as_trait};

use super::*;
use crate::INIT_STEP_NAME;
use crate::formula::function::builtin;
use crate::formula::function::inner::term_algebra::{self};

// =========================================================
// ======================= macros ==========================
// =========================================================

// FIXME!
macro_rules! unreachable_rules {
    ($span:expr, $urule:expr; $($rule:ident),*) => {
        // $span.wrong_rule(vec![$(Rule::$rule),+], vec![$urule])?
        unreachable!()
    };
}

macro_rules! debug_rule {
    ($p:ident, $($rule:ident)|+) => {
        if cfg!(debug_assertions) && match $p.as_rule() {
                $(Rule::$rule)|+ => false,
                _ => true
            }
        {
            unreachable_rules!($crate::parser::Location::from($p.as_span()),  $p.as_rule(); $($rule),*);
        }
    };
}

macro_rules! boiler_plate {
    ($t:ty, $lt:lifetime, $($rule:ident)|+; |$p:ident| $content:block) => {
        impl<$lt> TryFrom<Pair<$lt, Rule>> for $t {
            type Error = $crate::Error;

            fn try_from($p: Pair<$lt, Rule>) -> std::result::Result<$t, Self::Error> {
                let str = $p.as_str();
                trace!("parsing {str}");
                debug_rule!($p, $($rule)|+);

                let r = {$content};
                trace!("successfully parsed {str}");
                r
            }
        }
    };

    (l $t:ty, $lt:lifetime, $($rule:ident)|+; |$p:ident| { $($($pat:ident)|+ => $content:block)* }) => {
        boiler_plate!($t, 'a, $($rule)|+; |p| {
            #[allow(unused_variables)]
            let span = p.as_span();
            let mut p_iter = p.into_inner();
            let $p = p_iter.next().unwrap();

            if let Some(p) = p_iter.next() {
                $crate::bail_at!(p.as_span(), "too much")
                // return err(merr(p.as_span().into(), f!("too much")))
            }

            match $p.as_rule() {
                $(
                    $(Rule::$pat)|+ => $content,
                )*
                #[allow(unused_variables)]
                r => unreachable_rules!(span, r; $($($pat),+),*)
            }
        });
    };

    ($t:ty, $rule:ident; { $($pat:ident => $res:ident),* }) => {
        boiler_plate!(l $t, 'a, $rule; |p| {$($pat => { Ok(Self::$res) })*});
    };
    (@ $t:ident, $lt:lifetime, $($rule:ident)|+; |$p:ident| $content:block) => {
        boiler_plate!($t<$lt, &$lt str>, $lt, $($rule)|+; |$p| $content);
    }

}

macro_rules! as_array {
    ($span:ident in [$($arg:ident),*] = $vec:expr) => {
        destvec!{ [$($arg),*] = $vec; |err| {
            $crate::bail_at!($span, "{}", err)
        }}
    };

    ($span:ident in [$($arg:ident),*,..$leftover:ident] = $vec:expr) => {
        destvec!{ [$($arg),*,..$leftover] = $vec; |err| {
            // return Err(merr($span, f!("{}", err)))
            $crate::bail_at!($span, "{}", err)
        }}
    };
}

mod macro_helper {
    use pest::iterators::{Pair, Pairs};

    use super::Rule;

    pub trait AsInner<'a> {
        fn m_into_inner(self) -> Pairs<'a, Rule>;
    }

    impl<'a> AsInner<'a> for Pairs<'a, Rule> {
        fn m_into_inner(self) -> Pairs<'a, Rule> {
            self
        }
    }

    impl<'a> AsInner<'a> for Pair<'a, Rule> {
        fn m_into_inner(self) -> Pairs<'a, Rule> {
            self.into_inner()
        }
    }
}

macro_rules! destruct_rule {
    ($span:ident in [$($arg:ident),*] = $vec:expr) => {
        as_array!($span in [$($arg),*] = macro_helper::AsInner::m_into_inner($vec));
        $(
            let $arg = $arg.try_into().debug_continue()?;
        )*
    };

    ($span:ident in [$($arg:ident),*, ?$option:ident] = $vec:expr) => {
        as_array!($span in [$($arg),*,..leftover] = macro_helper::AsInner::m_into_inner($vec));
        $(
            let $arg = $arg.try_into().debug_continue()?;
        )*
        let $option = leftover.next().map(|r| r.try_into().debug_continue()).transpose()?.unwrap_or(Options::empty($span.into()));
        if let Some(_) = leftover.next() {
            $crate::bail_at!($span, "too many arguments")
            // return Err(merr($span, f!("too many arguments")))
        }
    }
}

// =========================================================
// ======================= parsing =========================
// =========================================================

/// All emcompassing struct like [AST], [ASTList] and [Declaration]
mod main;
pub use main::*;

/// Everything related to symbol sames, [Ident], [Function],...
mod ident;
pub use ident::*;

/// List of variables bindings
mod bindings;
pub use bindings::*;

/// [Term]
mod term;
pub use term::{InnerTerm, StrApplicable, Term};

/// Infix terms
mod infix;
pub use infix::*;

/// Function (and function like) applications
mod application;
pub use application::*;

/// `if then else`
mod if_then_else;
pub use if_then_else::*;

/// `find such that`
mod find_such_that;
pub use find_such_that::*;

/// Regular quantifiers (i.e., $\exits$ and $\forall$)
mod quantifier;
pub use quantifier::*;

/// **Not supported**
/// Let in
mod let_in;
pub use let_in::*;

/// Things related to types
mod sorts;
pub use sorts::*;

/// Things related to functions
mod functions;
pub use functions::*;

/// Things related to steps
mod step;
pub use step::*;

/// Things related to memory cells
mod cell;
pub use cell::*;

mod macros;
pub use macros::*;

mod options;
pub use options::*;

mod assertions;
pub use assertions::*;

mod ordering;
pub use ordering::*;

pub mod extra;
pub use extra::Sub;
