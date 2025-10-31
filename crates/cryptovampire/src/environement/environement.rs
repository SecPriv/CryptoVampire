use std::path::PathBuf;

use bitflags::bitflags;
use hashbrown::HashMap;
use utils::string_ref::StrRef;

use super::{
    // cli::Args,
    traits::{KnowsRealm, Realm},
};
use crate::container::ScopedContainer;
use crate::formula::function::Function;
use crate::runner::{VampireArg, VampireExec};

/// Super struct containing more or less the global state of cryptovampire
#[derive(Debug, Clone)]
pub struct Environement<'bump> {
    /// The container where all the [Function], ... are stored
    pub container: &'bump ScopedContainer<'bump>,
    realm: Realm,
    options: Options,
    solver_configuration: SolverConfig,
}

/// Gather flags for the configuration of cryptovampire
///
/// Since this can get confusing prefer using the functions of [Environement]
#[derive(Default, Clone, PartialEq, PartialOrd, Debug)]
pub struct Options {
    pub flags: Flags,
    pub rewrite_flags: RewriteFlags,
    pub subterm_flags: SubtermFlags,
}

bitflags! {
    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
    pub struct Flags: u16 {
        const LEMMA =                   1 << 0;
        const ASSERT_THEORY =           1 << 2; // non smt standard
        const SKOLEMNISE =              1 << 3;
        const LEGACY_EVALUATE =         1 << 4;
        const NO_BITSTRING =            1 << 5;
        const NOT_AS_TERM_ALGEBRA =     1 << 6;
        const ASSERT_NOT =              1 << 7; // non smt standard
        const ASSERT_GROUND =           1 << 8; // non smt standard
        const IGNORE_LEMMAS =           1 << 9;
        const DISALLOW_SHADOWING =      1 << 10;

        const NON_SMT_STANDARD =
            Flags::ASSERT_NOT.bits()
            | Flags::ASSERT_THEORY.bits()
            | Flags::ASSERT_GROUND.bits();
    }

    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
    pub struct RewriteFlags: u8 { // non standard
        const EVALUATE =                1 << 0;
        const CRYPTOGRAPHY =            1 << 1;
    }

    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
    pub struct SubtermFlags: u8 {
        const DEFINED =                 1 << 0;
        const PREPROCESS_INSTANCES =               1 << 1;
        const PREPROCESS_INPUTS =                  1 << 2 | SubtermFlags::DEFINED.bits();
        const PREPROCESS_CELLS =                   1 << 3 | SubtermFlags::DEFINED.bits();
        const VAMPIRE =                 1 << 4; // non smt standard

    }
}

impl<'bump> Environement<'bump> {
    pub fn new(
        container: &'bump ScopedContainer<'bump>,
        realm: Realm,
        options: Options,
        solver_configuration: SolverConfig,
    ) -> Self {
        Self {
            container,
            realm,
            options,
            solver_configuration,
        }
    }

    /// use `rewrite` in evaluate
    pub fn rewrite_evaluate(&self) -> bool {
        self.options.rewrite_flags.contains(RewriteFlags::EVALUATE)
    }

    /// use `rewrite` in crypto axioms
    pub fn rewrite_crypto(&self) -> bool {
        self.options
            .rewrite_flags
            .contains(RewriteFlags::CRYPTOGRAPHY)
    }

    /// preprocess crypto axioms as much as possible
    pub fn preprocess_instances(&self) -> bool {
        self.options
            .subterm_flags
            .contains(SubtermFlags::PREPROCESS_INSTANCES)
            || !self.define_subterm()
    }

    pub fn use_vampire_subterm(&self) -> bool {
        self.options.subterm_flags.contains(SubtermFlags::VAMPIRE) && self.is_symbolic_realm()
    }

    pub fn define_subterm(&self) -> bool {
        self.options.subterm_flags.contains(SubtermFlags::DEFINED)
    }

    /// Do not use the `(rewrite ...)` pseudo smt syntax for `vampire`
    pub fn no_rewrite(&self) -> bool {
        self.options.rewrite_flags.is_empty()
    }

    /// Use `assert-theory`
    pub fn use_assert_theory(&self) -> bool {
        self.options.flags.contains(Flags::ASSERT_THEORY)
    }

    /// Use `assert-not` for the query
    pub fn use_assert_not(&self) -> bool {
        self.options.flags.contains(Flags::ASSERT_NOT)
    }

    /// Use `assert-ground`
    pub fn use_assert_ground(&self) -> bool {
        self.options.flags.contains(Flags::ASSERT_GROUND)
    }

    /// Use the `legacy-evaluate`
    pub fn use_legacy_evaluate(&self) -> bool {
        self.options.flags.contains(Flags::LEGACY_EVALUATE) && self.is_symbolic_realm()
    }

    /// the evaluated realm is never used
    ///
    /// (but it still need to be defined for now, but no axioms should use it)
    pub fn no_bitstring_functions(&self) -> bool {
        self.options.flags.contains(Flags::NO_BITSTRING)
    }

    /// see [KnowsRealm]
    pub fn is_symbolic_realm(&self) -> bool {
        self.get_realm().is_symbolic()
    }

    /// see [KnowsRealm]
    pub fn is_evaluated_realm(&self) -> bool {
        self.get_realm().is_evaluated()
    }

    /// include the general crypto aximos
    pub fn with_general_crypto_axiom(&self) -> bool {
        // !self.not_as_term_algebra()
        self.is_symbolic_realm()
    }

    /// get the container with the right lifetime
    pub fn container_full_life_time(&self) -> &'bump ScopedContainer<'bump> {
        self.container
    }

    /// get a hashmat of the [Function]s currenlty defined
    pub fn get_function_hash(&self) -> HashMap<StrRef<'bump>, Function<'bump>> {
        self.container.get_function_hash_map()
    }

    /// do we fully ignore lemmas?
    pub fn are_lemmas_ignored(&self) -> bool {
        self.options.flags.contains(Flags::IGNORE_LEMMAS)
    }

    /// Are we running with the lemmas
    pub fn use_lemmas(&self) -> bool {
        self.options.flags.contains(Flags::LEMMA) && {
            assert!(!self.are_lemmas_ignored());
            true
        }
    }

    /// allow shadowing in the input files
    ///
    /// because `squirrel` loves them...
    pub fn allow_shadowing(&self) -> bool {
        !self.options.flags.contains(Flags::DISALLOW_SHADOWING)
    }

    pub fn options_mut(&mut self) -> &mut Options {
        &mut self.options
    }

    pub fn solver_configuration(&self) -> &SolverConfig {
        &self.solver_configuration
    }
}

impl<'bump> KnowsRealm for Environement<'bump> {
    fn get_realm(&self) -> super::traits::Realm {
        self.realm
    }
}

bitflags! {
    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
    pub struct EnabledSolvers : u8 {
        const VAMPIRE = 1<<0;
        const Z3 = 1<<1;
        const CVC5 = 1<<2;
    }
}

#[derive(Default, Clone, PartialEq, PartialOrd, Debug)]
pub struct SolverConfig {
    pub locations: Locations,
    pub enable_solvers: EnabledSolvers,
    pub num_of_retry: u32,
    pub timeout: f64,
    pub smt_debug: Option<PathBuf>,
}

#[derive(Default, Clone, PartialEq, PartialOrd, Debug)]
pub struct Locations {
    pub vampire: PathBuf,
    pub z3: PathBuf,
    pub cvc5: PathBuf,
}

impl SolverConfig {
    pub fn to_vampire_exec(&self) -> VampireExec {
        VampireExec {
            exe_location: self.locations.vampire.to_owned(),
            extra_args: vec![VampireArg::TimeLimit(self.timeout)],
        }
    }
}
