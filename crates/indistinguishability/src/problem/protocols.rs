use super::*;
use crate::mk_signature;
use crate::protocol::{Protocol, Step};
use crate::terms::{Function, FunctionFlags, INIT, InnerFunction};

impl Problem {
    /// Returns the `init` function
    pub fn get_init_fun(&self) -> &Function {
        &INIT
    }

    /// Returns the protocols
    pub fn protocols(&self) -> &[Protocol] {
        &self.protocols
    }

    /// Returns a mutable reference to the protocol at the given index
    pub fn protocol_mut(&mut self, index: usize) -> Option<&mut Protocol> {
        self.protocols.get_mut(index)
    }

    /// Simply declare a protocol, this one remains quite undefined
    pub fn declare_new_protocol(&mut self) -> &mut Protocol {
        self.clear_smt_prelude();
        let n = self.protocols.len();

        let inner = InnerFunction {
            flags: FunctionFlags::PROTOCOL,
            protocol_idx: n,
            ..InnerFunction::new(format!("_p${n:}").into(), mk_signature!(() -> Protocol))
        };
        let fun = Function::new(inner);
        self.function.add(fun.clone());

        let ptcl = {
            let builder = Protocol::builder().name(fun);
            if let Some(p0) = self.protocols().first() {
                builder
                    .steps(p0.steps().iter().map(|Step { id, vars, .. }| {
                        Step::builder()
                            .id(id.clone())
                            .vars(vars.clone())
                            .build()
                            .unwrap()
                    }))
                    .build()
            } else {
                builder.build()
            }
        };
        self.protocols.push(ptcl);
        &mut self.protocols[n]
    }

    /// Returns the number of protocols
    pub fn num_protocols(&self) -> usize {
        self.protocols().len()
    }
}
