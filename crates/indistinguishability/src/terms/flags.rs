use bitflags::bitflags;
use serde::{Deserialize, Serialize};

/// helper to write flags
macro_rules! const_fun_flags {
    ($id:ident) => {$crate::terms::FunctionFlags::$id};
    ($id0:ident | $($id:ident)|*) => {
        $crate::terms::FunctionFlags::$id0
            $(.union($crate::terms::FunctionFlags::$id))*
    };
}

bitflags! {
  #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, 
           Hash, Debug, Serialize, Deserialize)]
  pub struct FunctionFlags: u32 {
      /// The function is builtin
      const BUILTIN = 1 << 0;
      /// It's an alias for something else
      const ALIAS = 1 << 1;
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

      /// Has an equivalent built into smt
      const BUILTIN_SMT = 1 << 8;

      /// This is a nonce constructor
      const NONCE = 1 << 9;

      const CUSTOM_SUBTERM = 1 << 10;

      const SMT_ONLY = 1 << 11;
  }
}

pub static SHOULD_NOT_DECLARE_IN_SMT: FunctionFlags =
    const_fun_flags!(ALIAS | PROLOG_ONLY | BUILTIN_SMT);

pub static SPECIAL_SUBTERM: FunctionFlags = const_fun_flags!(
    ALIAS | PROLOG_ONLY | MACRO | UNFOLD | CUSTOM_SUBTERM
    | EXISTS | SKOLEM | NONCE | BUILTIN_SMT
);

pub static SPECIAL_DEDUCE: FunctionFlags = const_fun_flags!(
    ALIAS | PROLOG_ONLY | MACRO | UNFOLD | CUSTOM_DEDUCE
    | EXISTS | SKOLEM | NONCE | SMT_ONLY
);
