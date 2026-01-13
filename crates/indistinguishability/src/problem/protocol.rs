use std::num::NonZeroUsize;

use anyhow::{Context, anyhow, bail, ensure};

use super::*;
use crate::mk_signature;
use crate::protocol::{Protocol, Step};
use crate::terms::{Function, FunctionFlags, INCOMPATIBLE, INIT, InnerFunction, LT, Sort};

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

    /// Push steps to all protocols, returns a mutable pointer to those steps
    ///
    /// The ith steps is pushed to the ith protocol
    ///
    /// # Panics
    ///
    /// If the number if steps is different from the number of protocol or they use different [Function]
    pub fn push_steps(&mut self, steps: implvec!(Step)) -> Vec<&mut Step> {
        assert!(
            !self.protocols.is_empty(),
            "can't add steps to nothing! declare a protocol first!"
        );

        let mut steps = steps.into_iter().peekable();

        // update constrains
        {
            let id = steps.peek().expect("at least one step").id.clone();
            self.constrains_mut().push(Constrains {
                op: ConstrainOp::LessThan,
                arg1: BoundStep::init(),
                arg2: BoundStep {
                    head: id.clone(),
                    args: id.signature.mk_vars(),
                },
            });
        }

        let steps = steps
            .zip_eq(&mut self.protocols)
            .map(|(s, p)| p.add_step(s))
            .collect_vec();
        assert!(
            steps.iter().map(|s| &s.id).all_equal(),
            "The steps should all have the same name"
        );

        steps
    }

    /// Returns an iterator over the steps of the first protocol
    pub fn steps(&self) -> Option<impl Iterator<Item = Function> + use<'_>> {
        Some(
            self.protocols()
                .first()?
                .steps()
                .iter()
                .map(|Step { id, .. }| id.clone()),
        )
    }

    /// Returns the number of steps in the first protocol
    ///
    /// # Panics
    ///
    /// This function will panic if the first protocol has no steps.
    pub fn num_steps(&self) -> anyhow::Result<NonZeroUsize> {
        let n = self
            .protocols()
            .first()
            .with_context(|| "no protocols")?
            .steps()
            .len();
        let n = NonZeroUsize::new(n).with_context(|| {
            "a protocol has no steps, a protocol should always at least have an INIT step"
        })?;
        Ok(n)
    }

    pub fn declare_step(&mut self, name: String, sorts: Vec<Sort>) -> anyhow::Result<Function> {
        let n = self.num_steps()?.into();
        let step = self
            .declare_function()
            .inputs(sorts.iter().cloned())
            .step(n)
            .name(name)
            .call();
        let nptcl = self.num_protocols();
        self.push_steps((0..nptcl).map(|_| {
            Step::builder()
                .id(step.clone())
                .vars(sorts.iter().map(|&s| crate::fresh!(s)))
                .build()
                .unwrap()
        }));
        Ok(step)
    }

    /// returns the [Function] associated to the `index`th [Step] if it exists
    pub fn get_step_name(&self, index: usize) -> Option<&Function> {
        self.protocols().first()?.steps().get(index).map(|s| &s.id)
    }

    /// Returns a reference to the current step in the problem's execution, if any.
    pub(crate) fn current_step(&self) -> Option<&CurrentStep> {
        self.current_step.as_ref()
    }

    pub fn get_step_fun(&self, idx: usize) -> Option<&Function> {
        Some(&self.protocols.first()?.steps().get(idx)?.id)
    }

    pub fn constrains(&self) -> &[Constrains] {
        &self.constrains
    }

    pub fn constrains_mut(&mut self) -> &mut Vec<Constrains> {
        assert!(
            self.current_step.is_none(),
            "can't modify the constrains while the protocol is running"
        );
        &mut self.constrains
    }

    pub fn add_constrain(&mut self, constrain: &Formula) -> anyhow::Result<()> {
        match constrain {
            Formula::App { head, args } => {
                let op = if head == &LT {
                    ConstrainOp::LessThan
                } else if head == &INCOMPATIBLE {
                    ConstrainOp::Exclude
                } else {
                    bail!(
                        "not a valid operation.
                        The only valid ones are {LT} and {INCOMPATIBLE} (or '<>')"
                    )
                };

                let (a, b) = args
                    .iter()
                    .cloned()
                    .collect_tuple()
                    .with_context(|| "wrong number of arguments")?;
                let a = self.extract_step_and_vars(a)?;
                let b = self.extract_step_and_vars(b)?;

                self.constrains_mut().push(Constrains {
                    op,
                    arg1: a,
                    arg2: b,
                });
                Ok(())
            }
            _ => bail!("expected a function application"),
        }
    }

    fn extract_step_and_vars(&self, f: Formula) -> anyhow::Result<BoundStep> {
        match f {
            Formula::App { head, args } => {
                ensure!(
                    head.arity() == args.len(),
                    "wrong arity in step application"
                );
                let vars: anyhow::Result<Vec<_>> = args
                    .iter()
                    .map(|f| {
                        let var = f
                            .as_var()
                            .cloned()
                            .with_context(|| "all arguments should be variables")?;
                        // ensure!(var.has_sort(), "variables should have sorts");
                        var.maybe_set_sort(Some(Sort::Index)).map_err(|x| match x {
                            None => anyhow!("{var} is a static variable with no sort"),
                            Some(s) => anyhow!(
                                "{var} already has sort {s} and can't be set to {}",
                                Sort::Index
                            ),
                        })?;
                        Ok(var)
                    })
                    .collect();
                Ok(BoundStep { head, args: vars? })
            }
            f => bail!("{f} is not a function application"),
        }
    }
}
