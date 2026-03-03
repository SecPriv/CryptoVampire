use std::ops::{Deref, DerefMut};
use std::sync::{Arc, RwLock, RwLockWriteGuard};

use anyhow::Context;
use log::trace;
use steel::rerrs::ErrorKind;
use steel::rvals::{IntoSteelVal, Result as SResult};
use steel::steel_vm::builtin::BuiltInModule;
use steel::steel_vm::register_fn::RegisterFn;
use steel::{SteelErr, SteelVal};
use steel_derive::Steel;

use crate::input::golgge_rules::Rule;
use crate::input::shared_exists::ShrExists;
use crate::input::{BASE_LL_MODULE, Registerable, conversion_err};
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

    pub(crate) fn get_step_mut(
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
}

// =========================================================
// ========================= API ===========================
// =========================================================

/// Runs the indistinguishability check between two protocols.
#[steel_derive::declare_steel_function(name = "run")]
fn run(pbl: ShrProblem, p1: Function, p2: Function) -> SResult<bool> {
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
    Ok(pbl
        .borrow_mut()
        .run_solver(p1.protocol_idx, p2.protocol_idx))
}

/// Creates a new empty `Problem` instance with the given configuration.
#[steel_derive::declare_steel_function(name = "empty")]
fn mk_empty(config: Configuration) -> ShrProblem {
    let pbl = Problem::builder().config(config).build();
    ShrProblem(Arc::new(RwLock::new(pbl)))
}

/// Declares a new function in the problem.
#[steel_derive::declare_steel_function(name = "declare-function")]
fn declare_function(pbl: ShrProblem, fun: Function) -> Function {
    pbl.borrow_mut().functions_mut().add(fun.clone());
    fun
}

/// Declares a new protocol in the problem.
#[steel_derive::declare_steel_function(name = "declare-protocol")]
fn declare_protocol(pbl: ShrProblem) -> Function {
    pbl.borrow_mut().declare_new_protocol().name().clone()
}

/// Declares a new existential quantifier in the problem.
#[steel_derive::declare_steel_function(name = "declare-exists")]
fn declare_exists(pbl1: ShrProblem, captured: Vec<Sort>, bound: Vec<Sort>) -> ShrExists {
    let mut pbl = pbl1.borrow_mut();
    let exist = Exists::insert()
        .bvars_sorts(bound)
        .cvars_sorts(captured)
        .pbl(&mut pbl)
        .call();
    ShrExists {
        pbl: pbl1.clone(),
        index: exist.index().index,
    }
}

/// Adds a new rule to the problem.
#[steel_derive::declare_steel_function(name = "add-rule")]
fn add_rule(pbl: ShrProblem, Rule(r): Rule) {
    pbl.borrow_mut().extra_rules_mut().push(r);
}

/// Adds a new rewrite rule to the problem.
#[steel_derive::declare_steel_function(name = "add-rewrite")]
fn add_rewrite(pbl: ShrProblem, rw: Rewrite) {
    trace!("registering rw: \n{rw:#?}");
    pbl.borrow_mut().extra_rewrite_mut().push(rw);
}

/// Adds a new SMT axiom to the problem.
#[steel_derive::declare_steel_function(name = "add-smt-axiom")]
fn add_smt_axiom(pbl: ShrProblem, f: Formula) -> SResult<()> {
    let content = f
        .as_smt(pbl.borrow().deref())
        .ok_or(conversion_err::<MSmt>())?;
    pbl.borrow_mut()
        .extra_smt_mut()
        .push(MSmt::mk_assert(content));
    Ok(())
}

#[steel_derive::declare_steel_function(name = "add-constrain")]
fn add_constrain(pbl: ShrProblem, f: Formula) {
    pbl.borrow_mut()
        .add_constrain(&f)
        .with_context(|| format!("while in {f}"))
        .unwrap()
}

#[steel_derive::declare_steel_function(name = "publish")]
fn publish(pbl: ShrProblem, vars: Vec<Variable>, term: Formula) {
    pbl.borrow_mut().publish(PublicTerm { vars, term }).unwrap();
}

#[steel_derive::declare_steel_function(name = "get-report")]
fn get_report(pbl: ShrProblem) -> Report {
    pbl.0.read().unwrap().report.clone()
}

use paste::paste;
macro_rules! configuration {
    ($($id:ident : $t:ty),* $(,)?) => {
        $(
            paste!{
                #[doc = "gets the `" $id "` configuration field. See `--help` for documentation"]
                #[steel_derive::declare_steel_function(name = "[<get_ $id>]")]
                fn [<get_ $id>](pbl: ShrProblem) -> $t {
                    pbl.borrow().config.$id.clone()
                }

                #[doc = "sets the `" $id "` configuration field. See `--help` for documentation"]
                #[steel_derive::declare_steel_function(name = "[<set_ $id>]")]
                fn [<set_ $id>](pbl: ShrProblem, value:$t) {
                    pbl.borrow_mut().config.$id = value;
                }
            }
        )*

        fn register_configuration( module: &mut BuiltInModule) -> &mut BuiltInModule {
                paste! {
                module
                $(
                    .register_native_fn_definition([<GET_ $id:upper _DEFINITION>])
                    .register_native_fn_definition([<SET_ $id:upper _DEFINITION>])
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
    fn register(modules: &mut rustc_hash::FxHashMap<String, BuiltInModule>) {
        {
            let name = "crypotvampire/ll/configuration";
            let mut module = BuiltInModule::new(name);
            register_configuration(&mut module);
            trace!("defined {name} scheme module");
            assert!(modules.insert(name.into(), module).is_none());
        }
        {
            let name = "cryptovampire/ll/pbl";
            let mut module = BuiltInModule::new(name);

            module
                .register_type::<Self>("Problem?")
                .register_native_fn_definition(RUN_DEFINITION)
                .register_native_fn_definition(MK_EMPTY_DEFINITION)
                .register_native_fn_definition(DECLARE_FUNCTION_DEFINITION)
                .register_native_fn_definition(DECLARE_PROTOCOL_DEFINITION)
                .register_native_fn_definition(DECLARE_EXISTS_DEFINITION)
                .register_native_fn_definition(ADD_RULE_DEFINITION)
                .register_native_fn_definition(ADD_REWRITE_DEFINITION)
                .register_native_fn_definition(ADD_SMT_AXIOM_DEFINITION)
                .register_native_fn_definition(ADD_CONSTRAIN_DEFINITION)
                .register_native_fn_definition(PUBLISH_DEFINITION)
                .register_native_fn_definition(GET_REPORT_DEFINITION);

            trace!("defined {name} scheme module");
            assert!(modules.insert(name.into(), module).is_none());
        }
        {
            let module = modules.get_mut(BASE_LL_MODULE).unwrap();

            module.register_fn("string->duration", |s: String| {
                humantime::parse_duration(&s).unwrap()
            });
        }
    }
}
