use std::path::PathBuf;

use crate::{container::ScopedContainer, formula::function::Function};

use bitflags::bitflags;
use hashbrown::HashMap;
use utils::string_ref::StrRef;

use super::{
    // cli::Args,
    traits::{KnowsRealm, Realm},
};

#[derive(Debug, Clone)]
pub struct Environement<'bump> {
    pub container: &'bump ScopedContainer<'bump>,
    realm: Realm,
    options: Options,
}

#[derive(Default, Clone, PartialEq, PartialOrd, Debug)]
pub struct Options {
    pub flags: Flags,
    pub rewrite_flags: RewriteFlags,
    pub subterm_flags: SubtermFlags,
    pub automated_vampire: Option<AutomatedVampire>,
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
    pub fn new(container: &'bump ScopedContainer<'bump>, realm: Realm, options: Options) -> Self {
        Self {
            container,
            realm,
            options,
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

    pub fn no_rewrite(&self) -> bool {
        self.options.rewrite_flags.is_empty()
    }

    pub fn use_assert_theory(&self) -> bool {
        self.options.flags.contains(Flags::ASSERT_THEORY)
    }

    pub fn use_assert_not(&self) -> bool {
        self.options.flags.contains(Flags::ASSERT_NOT)
    }

    pub fn use_assert_ground(&self) -> bool {
        self.options.flags.contains(Flags::ASSERT_GROUND)
    }

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

    pub fn with_general_crypto_axiom(&self) -> bool {
        // !self.not_as_term_algebra()
        self.is_symbolic_realm()
    }

    pub fn container_full_life_time(&self) -> &'bump ScopedContainer<'bump> {
        self.container
    }

    pub fn get_function_hash(&self) -> HashMap<StrRef<'bump>, Function<'bump>> {
        self.container.get_function_hash_map()
    }

    pub fn get_automated_vampire(&self) -> Option<&AutomatedVampire> {
        self.options.automated_vampire.as_ref()
    }
}

impl<'bump> KnowsRealm for Environement<'bump> {
    fn get_realm(&self) -> super::traits::Realm {
        self.realm
    }
}

#[derive(Default, Clone, PartialEq, PartialOrd, Debug)]
pub struct AutomatedVampire {
    pub location: PathBuf,
    pub num_retry: u32,
    pub exec_time: f64,
    pub smt_debug: Option<PathBuf>,
}
