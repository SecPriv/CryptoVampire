//! Call graph
//!
//! Note that all the nomenclature is base on `input(T)` is a "call" to `T`, hence `init` is a descendant to everyone.

use std::num::{NonZeroU32, NonZeroUsize};
use std::rc::Rc;

use crate::terms::{Formula, Function, Variable};

// =========================================================
// ===================== index types =======================
// =========================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct StepRef(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ProtocolRef(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CellRef(pub NonZeroUsize);

// =========================================================
// ===================== call types ========================
// =========================================================

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CellCall {
    pub cell: CellRef,
    pub args: Vec<Variable>,
}

/// A macro call without protocol
///
/// This is loosly an index in an array
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PreCall {
    Exec(StepRef),
    Frame(StepRef),
    Cell { cell: CellRef, time: StepRef },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallCallee {
    /// +/- ptr to [Caller]
    pub call: PreCall,
    /// how deeply nested in `pred` it is
    pub num_preds: usize,
    /// the new variables for step
    pub step_vars: Vec<Variable>,
    /// the new variables for cell, whatever if irrelevant
    pub cell_vars: Vec<Variable>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Caller {
    pub callees: Vec<CallCallee>,
}

// =========================================================
// ======================== graph ==========================
// =========================================================

#[derive(Debug, Clone)]
pub struct Graph {
    cell_num: usize,
    callers: Vec<Caller>,
    initialized: bool,
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
    pub struct DescendantFlags: u8 {
        const Plain = 1 << 0;
        const Pred = 1 << 1;
    }
}

mod graph;

impl<'a> TryFrom<&'a Function> for CellRef {
    type Error = &'a Function;

    fn try_from(value: &'a Function) -> Result<Self, Self::Error> {
        match value.get_cell_index() {
            Some(i) => Ok(Self(NonZeroUsize::new(i + 1).unwrap())),
            None => Err(value),
        }
    }
}

impl TryFrom<Function> for CellRef {
    type Error = Function;

    fn try_from(value: Function) -> Result<Self, Self::Error> {
        match value.get_cell_index() {
            Some(i) => Ok(Self(NonZeroUsize::new(i + 1).unwrap())),
            None => Err(value),
        }
    }
}
