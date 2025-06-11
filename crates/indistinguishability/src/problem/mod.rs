use std::{borrow::Cow, collections::HashMap};

use egg::{Analysis, EGraph};
use itertools::Itertools;

use crate::{
    Configuration, Lang, mk_signature,
    protocol::Protocol,
    terms::{Function, FunctionCollection, FunctionFlags, InnerFunction},
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

    /// Simply declare a protocol, this one remains quite undefined
    pub fn declare_new_protocol(&mut self) -> &mut Protocol {
        let n = self.protocols.len();

        let inner = InnerFunction {
            flags: FunctionFlags::PROTOCOL,
            protocol_idx: n,
            ..InnerFunction::new(format!("_p${n:}").into(), mk_signature!(() -> Protocol))
        };
        let fun = Function::new(inner);
        self.function.add(fun.clone());

        let ptcl = Protocol::new(fun);
        self.protocols.push(ptcl);
        &mut self.protocols[n]
    }
}

impl AsRef<FunctionCollection> for Problem {
    fn as_ref(&self) -> &FunctionCollection {
        &self.function
    }
}

impl AsMut<FunctionCollection> for Problem {
    fn as_mut(&mut self) -> &mut FunctionCollection {
        &mut self.function
    }
}

#[cfg(test)]
pub mod test;
