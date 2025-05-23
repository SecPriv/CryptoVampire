use std::{borrow::Cow, collections::HashMap};

use itertools::Itertools;

use crate::{
    protocol::Protocol,
    terms::{Function, FunctionCollection},
    Configuration, Lang,
};

/// A problem for the solver to solve
#[derive(Debug, Default)]
pub struct Problem {
    /// The configuration (e.g., cli arguments and such)
    pub config: Configuration,
    /// The protocol we want to prove indistiguishability on
    ///
    /// The vector must be at least 2 long
    pub protocols: Vec<Protocol>,
    /// The functions
    pub function: FunctionCollection,
}

impl Problem {
    pub fn base_empty() -> Self {
        Self {
            config: Default::default(),
            protocols: Default::default(),
            function: FunctionCollection::init(),
        }
    }

    pub fn valid(&self) -> bool {
        self.protocols
            .iter()
            .tuple_windows()
            .all(|(a, b)| Protocol::are_compatible(a, b))
    }
}
