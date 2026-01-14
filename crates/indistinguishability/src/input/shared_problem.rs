use std::ops::{Deref, DerefMut};
use std::sync::{Arc, RwLock, RwLockWriteGuard};

use anyhow::Context;
use log::trace;
use steel::SteelErr;
use steel::rerrs::ErrorKind;
use steel::rvals::Result as SResult;
use steel::steel_vm::builtin::BuiltInModule;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::golgge_rules::Rule;
use crate::input::shared_exists::ShrExists;
use crate::input::{Registerable, conversion_err};
use crate::problem::{PublicTerm, Report};
use crate::protocol::Step;
use crate::terms::{Exists, Formula, Function, QuantifierT, Rewrite, Sort, Variable};
use crate::{Configuration, MSmt, Problem};

declare_trace!($"shrpblm");

/// A shared, reference-counted, mutable problem instance for use within the Steel VM.
#[derive(Debug, Clone, Steel)]
pub struct ShrProblem(pub(crate) Arc<RwLock<Problem>>);

impl ShrProblem {
    /// Borrows the underlying `Problem` immutably.
    pub fn borrow(&self) -> impl Deref<Target = Problem> {
        self.0.read().unwrap()
    }

    /// Borrows the underlying `Problem` mutably.
    pub fn borrow_mut(&self) -> impl DerefMut<Target = Problem> {
        self.0.write().unwrap()
    }

    fn get_step_mut(
        &self,
        step: Function,
        ptcl: Function,
    ) -> SResult<impl DerefMut<Target = Step>> {
        if !step.is_step() {
            return Err(SteelErr::new(
                ErrorKind::ConversionError,
                format!("'step' ({step}) should be a step"),
            ));
        }

        if !ptcl.is_protocol() {
            return Err(SteelErr::new(
                ErrorKind::ConversionError,
                format!("'ptcl' ({ptcl}) should be a protocol"),
            ));
        }

        let step = RwLockWriteGuard::map(self.0.write().unwrap(), |x| {
            x.protocol_mut(ptcl.protocol_idx)
                .unwrap()
                .step_mut(step.step_idx)
                .unwrap()
        });
        Ok(step)
    }

    // =========================================================
    // ========================= API ===========================
    // =========================================================
    /// Runs the indistinguishability check between two protocols.
    fn run(&self, p1: Function, p2: Function) -> SResult<bool> {
        if !p1.is_protocol() {
            return Err(SteelErr::new(
                ErrorKind::ConversionError,
                format!("{p1} is not a protocol"),
            ));
        }
        if !p2.is_protocol() {
            return Err(SteelErr::new(
                ErrorKind::ConversionError,
                format!("{p2} is not a protocol"),
            ));
        }
        Ok(self
            .borrow_mut()
            .run_solver(p1.protocol_idx, p2.protocol_idx))
    }

    /// Creates a new empty `Problem` instance with the given configuration.
    fn mk_empty(config: Configuration) -> Self {
        let pbl = Problem::builder().config(config).build();
        Self(Arc::new(RwLock::new(pbl)))
    }

    /// Declares a new function in the problem.
    fn declare_function(self, fun: Function) -> Function {
        self.borrow_mut().functions_mut().add(fun.clone());
        fun
    }

    /// Declares a new step function in the problem.
    fn declare_step(&self, name: String, sorts: Vec<Sort>) -> SResult<Function> {
        match self.borrow_mut().declare_step(name, sorts) {
            Err(e) => Err(SteelErr::new(ErrorKind::Generic, e.to_string())),
            Ok(s) => Ok(s),
        }
    }

    /// Declares a new protocol in the problem.
    fn declare_protocol(&self) -> Function {
        self.borrow_mut().declare_new_protocol().name().clone()
    }

    /// Declares a new existential quantifier in the problem.
    fn declare_exists(&self, captured: Vec<Sort>, bound: Vec<Sort>) -> ShrExists {
        let mut pbl = self.borrow_mut();
        let exist = Exists::insert()
            .bvars_sorts(bound)
            .cvars_sorts(captured)
            .pbl(&mut pbl)
            .call();
        ShrExists {
            pbl: self.clone(),
            index: exist.index().index,
        }
    }

    /// Sets the variables for a given step in a protocol.
    fn set_step_vars(&self, step: Function, ptcl: Function, vars: Vec<Variable>) -> SResult<()> {
        let mut step = self.get_step_mut(step, ptcl)?;

        if step.id.arity() != vars.len() {
            return Err(SteelErr::new(
                ErrorKind::Generic,
                format!(
                    "wrong number of step variables ({} instead of {})",
                    vars.len(),
                    step.id.arity()
                ),
            ));
        }

        step.vars = vars;
        Ok(())
    }

    /// Returns the variables for a given step in a protocol.
    fn get_step_vars(&self, step: Function, ptcl: Function) -> SResult<Vec<Variable>> {
        Ok(self.get_step_mut(step, ptcl)?.vars.clone())
    }

    /// Sets the message for a given step in a protocol.
    fn set_step_msg(&self, step: Function, ptcl: Function, msg: Formula) -> SResult<()> {
        self.get_step_mut(step, ptcl)?.msg = msg;
        Ok(())
    }

    /// Sets the condition for a given step in a protocol.
    fn set_step_cond(&self, step: Function, ptcl: Function, cond: Formula) -> SResult<()> {
        self.get_step_mut(step, ptcl)?.cond = cond;
        Ok(())
    }

    /// Adds a new rule to the problem.
    fn add_rule(&self, Rule(r): Rule) {
        self.borrow_mut().extra_rules_mut().push(r);
    }

    /// Adds a new rewrite rule to the problem.
    fn add_rewrite(&self, rw: Rewrite) {
        trace!("registering rw: \n{rw:#?}");
        self.borrow_mut().extra_rewrite_mut().push(rw);
    }

    /// Adds a new SMT axiom to the problem.
    fn add_smt_axiom(&self, f: Formula) -> SResult<()> {
        let content = f
            .as_smt(self.borrow().deref())
            .ok_or(conversion_err::<MSmt>())?;
        self.borrow_mut()
            .extra_smt_mut()
            .push(MSmt::mk_assert(content));
        Ok(())
    }

    fn add_constrain(&self, f: Formula) {
        self.borrow_mut()
            .add_constrain(&f)
            .with_context(|| format!("while in {f}"))
            .unwrap()
    }

    fn publish(&self, vars: Vec<Variable>, term: Formula) {
        self.borrow_mut()
            .publish(PublicTerm { vars, term })
            .unwrap();
    }

    fn get_report(&self) -> Report {
        self.0.read().unwrap().report.clone()
    }

    // =========================================================
    // ====================== printing =========================
    // =========================================================

    /// Returns a string representation of a specific step in a protocol.
    fn to_string_step(&self, ptcl: Function, step: Function) -> SResult<String> {
        let Some(pidx) = ptcl.get_protocol_index() else {
            return Err(SteelErr::new(
                ErrorKind::ConversionError,
                format!("{ptcl} (ptcl) isn't a protocol"),
            ));
        };
        let Some(sidx) = step.get_step_index() else {
            return Err(SteelErr::new(
                ErrorKind::ConversionError,
                format!("{step} (step) isn't a step"),
            ));
        };

        let pbl = self.borrow();
        let step = &pbl.protocols()[pidx].steps()[sidx];
        Ok(format!("{step}"))
    }
}

use paste::paste;
macro_rules! configuration {
    ($($id:ident : $t:ty),* $(,)?) => {
        impl ShrProblem {
            $(
                paste!{
                    fn [<get_ $id>](&self) -> $t {
                        self.borrow().config.$id.clone()
                    }

                    fn [<set_ $id>](&self, value:$t) {
                        self.borrow_mut().config.$id = value;
                    }
                }
            )*

            fn register_configuration( module: &mut BuiltInModule) -> &mut BuiltInModule {
                module
                $(
                    .register_fn(String::leak(paste!(std::stringify!([<get_ $id>]).replace('_', "-"))), paste!(Self::[<get_ $id>]))
                    .register_fn(String::leak(paste!(std::stringify!([<set_ $id>]).replace('_', "-"))), paste!(Self::[<set_ $id>]))
                )*
            }
        }
    };
}

configuration!(
    node_limit: usize,
    iter_limit: usize,
    time_limit: std::time::Duration,
    vampire_timeout: std::time::Duration,
    cores: u64,
    trace: bool,
    trace_rebuilds:bool,
    keep_smt_files:bool,

    prf_limit:usize,
    fa_limit:usize,
    enc_kp_limit:usize,
    ddh_limit:usize,
    guided_nonce_search: bool,
);

impl Registerable for ShrProblem {
    /// Registers the `ShrProblem` type and its associated functions with the Steel VM.
    fn register(module: &mut BuiltInModule) -> &mut BuiltInModule {
        Self::register_type(module);
        Self::register_configuration(module);

        module
            .register_fn("to-string-step", Self::to_string_step)
            .register_fn("empty-problem", Self::mk_empty)
            .register_fn("declare-function", Self::declare_function)
            .register_fn("declare-protocol", Self::declare_protocol)
            .register_fn("declare-exists", Self::declare_exists)
            // .register_fn("declare-find-such-that", Self::declare_fdst)
            .register_fn("declare-step", Self::declare_step)
            .register_fn("set-step-message", Self::set_step_msg)
            .register_fn("set-step-condition", Self::set_step_cond)
            .register_fn("set-step-vars", Self::set_step_vars)
            .register_fn("get-step-variables", Self::get_step_vars)
            .register_fn("add-rule", Self::add_rule)
            .register_fn("add-rewrite", Self::add_rewrite)
            .register_fn("add-smt-axiom", Self::add_smt_axiom)
            .register_fn("add-constrain", Self::add_constrain)
            .register_fn("publish", Self::publish)
            .register_fn("get-report", Self::get_report)
            .register_fn("get-config", |x: Self| x.0.read().unwrap().config.clone())
            .register_fn("run", Self::run);

        Self::register_configuration(module).register_fn("string->duration", |s: String| {
            humantime::parse_duration(&s).unwrap()
        });

        module
    }
}
