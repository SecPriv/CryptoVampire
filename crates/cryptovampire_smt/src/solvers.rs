use core::fmt;
use std::fmt::Display;

use rustc_hash::FxHashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum Solver {
    Vampire,
    Cvc5,
    Z3,
    #[default]
    Generic,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SolverFeatures {
    AssertNot,
    AssertTh,
    AssertGround,
    Rewrite,
    Subterm,
}

impl Display for Solver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Vampire => write!(f, "vampire"),
            Self::Cvc5 => write!(f, "cvc5"),
            Self::Z3 => write!(f, "z3"),
            Self::Generic => write!(f, "generic smt solver"),
        }
    }
}

impl Solver {
    pub fn reserved_keywords(self) -> &'static FxHashSet<&'static str> {
        use crate::solvers::reserved_keywords::*;
        match self {
            Self::Vampire => &VAMPIRE,
            Self::Cvc5 => &CVC5,
            Self::Z3 => &Z3,
            Self::Generic => &SMT,
        }
    }
}

mod reserved_keywords {
    use rustc_hash::FxHashSet;
    use static_init::dynamic;

    fn mk_reserved(str: &'static str) -> FxHashSet<&'static str> {
        str.lines().map(str::trim).collect()
    }

    #[dynamic]
    pub static VAMPIRE: FxHashSet<&'static str> =
        mk_reserved(include_str!("../assets/reserved_keywords/vampire.txt"));

    #[dynamic]
    pub static Z3: FxHashSet<&'static str> =
        mk_reserved(include_str!("../assets/reserved_keywords/z3.txt"));

    #[dynamic]
    pub static CVC5: FxHashSet<&'static str> =
        mk_reserved(include_str!("../assets/reserved_keywords/cvc5.txt"));

    #[dynamic]
    pub static SMT: FxHashSet<&'static str> =
        mk_reserved(include_str!("../assets/reserved_keywords/smt.txt"));
}

impl Display for SolverFeatures {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name().fmt(f)
    }
}

impl SolverFeatures {
    pub const fn name(self) -> &'static str {
        match self {
            Self::AssertNot => "assert-not",
            Self::AssertTh => "assert-th",
            Self::AssertGround => "assert-ground",
            Self::Rewrite => "cryptovmapire rewrite",
            Self::Subterm => "cryptovampire subterm",
        }
    }
}
