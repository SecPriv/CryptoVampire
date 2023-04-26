use crate::container::Container;

use bitflags::bitflags;

#[derive(Debug, Clone)]
pub struct Environement<'bump> {
    pub container: &'bump Container<'bump>,
    options: Options,
}

#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Options {
    flags: Flags,
    rewrite_flags: RewriteFlags,
    subterm_flags: SubtermFlags,
}

bitflags! {
    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
    struct Flags: u8 {
        const LEMMA =                   1 << 0;
        const ASSERT_THEORY =           1 << 2; // non smt standard
        const SKOLEMNISE =              1 << 3;
        const LEGACY_EVALUATE =         1 << 4;
        const NO_BITSTRING =            1 << 5;
        const NOT_AS_TERM_ALGEBRA =     1 << 6;
        const ASSERT_NOT =              1 << 7; // non smt standard
    }

    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
    struct RewriteFlags: u8 { // non standard
        const EVALUATE =                1 << 0;
        const CRYPTOGRAPHY =            1 << 1;
    }

    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
    struct SubtermFlags: u8 {
        const DEFINED =                 1 << 0;
        const PREPROCESS_INSTANCES =               1 << 1;
        const PREPROCESS_INPUTS =                  1 << 2 | SubtermFlags::DEFINED.bits();
        const PREPROCESS_CELLS =                   1 << 3 | SubtermFlags::DEFINED.bits();
        const VAMPIRE =                 1 << 4; // non smt standard

    }
}

impl<'bump> Environement<'bump> {
    pub fn rewrite_evaluate(&self) -> bool {
        self.options.rewrite_flags.contains(RewriteFlags::EVALUATE)
    }

    pub fn rewrite_crypto(&self) -> bool {
        self.options
            .rewrite_flags
            .contains(RewriteFlags::CRYPTOGRAPHY)
    }

    pub fn preprocess_instances(&self) -> bool {
        self.options
            .subterm_flags
            .contains(SubtermFlags::PREPROCESS_INSTANCES)
            || !self.define_subterm()
    }

    pub fn preprocess_inputs(&self) -> bool {
        self.options
            .subterm_flags
            .contains(SubtermFlags::PREPROCESS_INPUTS)
    }

    pub fn preprocess_cell(&self) -> bool {
        self.options
            .subterm_flags
            .contains(SubtermFlags::PREPROCESS_CELLS)
    }

    pub fn use_vampire_subterm(&self) -> bool {
        self.options.subterm_flags.contains(SubtermFlags::VAMPIRE)
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

    pub fn skolemnise(&self) -> bool {
        self.options.flags.contains(Flags::SKOLEMNISE)
    }

    pub fn use_legacy_evaluate(&self) -> bool {
        self.options.flags.contains(Flags::LEGACY_EVALUATE) && !self.no_evaluate()
    }

    pub fn no_bitstring(&self) -> bool {
        self.options.flags.contains(Flags::NO_BITSTRING)
    }

    pub fn use_bitstring(&self) -> bool {
        !self.no_bitstring() && !self.no_evaluate()
    }

    pub fn no_evaluate(&self) -> bool {
        self.not_as_term_algebra()
    }

    pub fn not_as_term_algebra(&self) -> bool {
        self.options.flags.contains(Flags::NOT_AS_TERM_ALGEBRA)
    }

    pub fn with_general_crypto_axiom(&self) -> bool {
        !self.not_as_term_algebra()
    }

    pub fn container_full_life_time(&self) -> &'bump Container<'bump> {
        self.container
    }
}
