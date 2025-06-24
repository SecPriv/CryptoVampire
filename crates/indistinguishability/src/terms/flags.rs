use bitflags::bitflags;
use serde::{Deserialize, Serialize};

bitflags! {
  #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
           Hash, Debug, Serialize, Deserialize)]
  pub struct FunctionFlags: u32 {
      /// The function is builtin
      const BUILTIN = 1 << 0;
      /// It's an alias for something else
      // const ALIAS = 1 << 1;
      /// Appears only in prolog
      const PROLOG_ONLY = 1 << 2;

      /// Is a macro
      const MACRO = 1 << 3;
      /// Is an unfolding function
      const UNFOLD = 1 << 4;

      /// Necesitate a customize deduce that does
      /// not fit in any category
      const CUSTOM_DEDUCE = 1 << 5;

      /// Represents an existential quantifier
      const EXISTS = 1 << 6;
      /// Represents a skolem function
      const SKOLEM = 1 << 7;
      const EXISTS_FRESH = 1<< 8;

      /// Has an equivalent built into smt
      const BUILTIN_SMT = 1 << 9;

      /// This is a nonce constructor
      const NONCE = 1 << 10;

      const CUSTOM_SUBTERM = 1 << 11;

      const SMT_ONLY = 1 << 12;

      /// Is a protocol
      const PROTOCOL = 1 << 13;
      /// Is a step
      const STEP = 1 << 14;
  }
}
