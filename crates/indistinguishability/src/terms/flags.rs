use bitflags::bitflags;
use serde::{Deserialize, Serialize};

bitflags! {
  #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
           Hash, Debug, Serialize, Deserialize)]
  pub struct FunctionFlags: u32 {
      /// The function is builtin
      const BUILTIN = 1 << 0;
      /// Appears only in prolog
      const PROLOG_ONLY = 1 << 2;

      /// Is a macro
      const MACRO = 1 << 3;
      /// Is an unfolding function
      const UNFOLD = 1 << 4;

      /// Necesitate a customize deduce that does
      /// not fit in any category
      const CUSTOM_DEDUCE = 1 << 5;

      const BINDER = 1 << 6;
      const FIND_SUCH_THAT = 1 << 7;
      /// Represents a skolem function
      const SKOLEM = 1 << 8;
      const QUANTIFIER_FRESH = 1<< 9;

      /// Has an equivalent built into smt
      const BUILTIN_SMT = 1 << 10;

      /// This is a nonce constructor
      const NONCE = 1 << 11;

      const CUSTOM_SUBTERM = 1 << 12;

      const SMT_ONLY = 1 << 13;

      /// Is a protocol
      const PROTOCOL = 1 << 14;
      /// Is a step
      const STEP = 1 << 15;

      /// Is an `if .. then .. else` function
      const IF_THEN_ELSE = 1 << 16;

      /// This represents a [Sort]
      const SORT = 1 << 17;

      const LIST_CONSTR = 1 << 18;
      const LIST_FA_CONSTR = 1 << 19;

      /// This function is temporary and should be garabage collected as soon as
      /// possible.
      ///
      /// This can be used for temporary quantifiers for instance.
      const TEMPORARY = 1 << 20;

      const LAMBDA = 1 << 21;

      const FRESH = 1 << 22;

      /// This step is a publication step
      const PUBLICATION_STEP = 1 << 23;
  }
}
