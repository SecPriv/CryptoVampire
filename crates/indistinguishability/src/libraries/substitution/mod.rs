//! definition of the `subst` rewrite rules
//!
//! ```text
//! subst(m, x, y) -> m[x -> y]
//! ```

use std::collections::hash_map::Entry;
use std::rc::Rc;

use egg::{Analysis, EGraph, Id, Language, Pattern};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use static_init::dynamic;
use utils::transposer::VecTranspose;

// use crate::rules::base_rules::substitution;
// use crate::rules::utils::mk_subst_rw;
use crate::terms::{
    Function, FunctionFlags, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, PRED, SUBSTITUTION,
    SUBSTITUTION_RULE,
};
use crate::{Lang, rexp};

declare_trace!($"substitution");

pub use rule::SubstLib;
mod rule;

mod algorithm;

mod from_proof;
pub use from_proof::{PSArgs, ProofLike, ProofSubstitution};

decl_vars!(const; GOAL:Bool, X:Any, FROM:Bitstring, TO:Bitstring, PTCL:Protocol, T:Time);

#[dynamic]
static SUBSTITUTION_RULE_PATTERN: Pattern<Lang> = Pattern::from(&rexp!((SUBSTITUTION_RULE #GOAL)));

#[dynamic]
static SUBSTITUTION_PATTERN: Pattern<Lang> = Pattern::from(&rexp!((SUBSTITUTION #X #FROM #TO)));

#[dynamic]
static ACCEPTABLY_EMPTY: Vec<Pattern<Lang>> = {
    vec![
        Pattern::from(&rexp!((MACRO_EXEC (PRED #T) #PTCL))),
        Pattern::from(&rexp!((MACRO_FRAME (PRED #T) #PTCL))),
        Pattern::from(&rexp!((MACRO_INPUT #T #PTCL))),
    ]
};

fn is_ok_for_substitution(f: &Function) -> bool {
    f.is_ok_for_substitution()
        && (!f
            .flags
            .intersects(FunctionFlags::MACRO | FunctionFlags::UNFOLD))
}
