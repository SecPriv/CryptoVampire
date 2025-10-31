use std::cell::{Ref, RefCell, RefMut};
use std::ops::Deref;
use std::rc::Rc;

use steel::SteelErr;
use steel::rerrs::ErrorKind;
use steel::rvals::Result as SResult;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::golgge_rules::Rule;
use crate::input::shared_exists::ShrExists;
use crate::input::shared_fdst::ShrFindSuchThat;
use crate::input::{Registerable, conversion_err};
use crate::protocol::Step;
use crate::terms::{
    Exists, FindSuchThat, Function, QuantifierT, RecFOFormula, Rewrite, Sort, Variable,
};
use crate::{Configuration, MSmt, Problem};

declare_trace!($"shrpblm");

#[derive(Debug, Clone, Steel)]
pub struct ShrProblem(Rc<RefCell<Problem>>);

impl ShrProblem {
    pub fn borrow(&self) -> Ref<'_, Problem> {
        self.0.borrow()
    }

    pub fn borrow_mut(&self) -> RefMut<'_, Problem> {
        self.0.borrow_mut()
    }

    /// returns [None] is the shared pointer is still shared
    #[allow(dead_code)]
    pub fn try_into_inner(self) -> Option<Problem> {
        Rc::into_inner(self.0).map(RefCell::into_inner)
    }

    fn get_step_mut(&self, step: Function, ptcl: Function) -> SResult<RefMut<'_, Step>> {
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

        let step = RefMut::map(self.borrow_mut(), |x| {
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
        Ok(self.borrow_mut().run(p1.protocol_idx, p2.protocol_idx))
    }

    fn mk_empty(config: Configuration) -> Self {
        let pbl = Problem::builder().config(config).build();
        Self(Rc::new(RefCell::new(pbl)))
    }

    fn declare_function(self, fun: Function) -> Function {
        self.borrow_mut().functions_mut().add(fun.clone());
        fun
    }

    fn declare_step(&self, name: String, sorts: Vec<Sort>) -> SResult<Function> {
        let mut pbl = self.borrow_mut();

        let Some(steps) = pbl.steps() else {
            return Err(SteelErr::new(
                ErrorKind::Generic,
                "can't declare step function, you need to declare at least one protocol first"
                    .into(),
            ));
        };
        let n = steps.count();
        let step = pbl
            .declare_function()
            .inputs(sorts.iter().cloned())
            .step(n)
            .name(name)
            .call();
        let nptcl = pbl.num_protocols();
        pbl.push_steps((0..nptcl).map(|_| {
            Step::builder()
                .id(step.clone())
                .vars(sorts.iter().map(|&s| crate::fresh!(s)))
                .build()
                .unwrap()
        }));
        Ok(step)
    }

    fn declare_protocol(&self) -> Function {
        self.borrow_mut().declare_new_protocol().name().clone()
    }

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

    fn declare_fdst(&self, captured: Vec<Sort>, bound: Vec<Sort>) -> ShrFindSuchThat {
        let mut pbl = self.borrow_mut();
        let fdst = FindSuchThat::insert()
            .bvars_sorts(bound)
            .cvars_sorts(captured)
            .pbl(&mut pbl)
            .call();
        ShrFindSuchThat {
            pbl: self.clone(),
            index: fdst.index().index,
        }
    }

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

    fn get_step_vars(&self, step: Function, ptcl: Function) -> SResult<Vec<Variable>> {
        Ok(self.get_step_mut(step, ptcl)?.vars.clone())
    }

    fn set_step_msg(&self, step: Function, ptcl: Function, msg: RecFOFormula) -> SResult<()> {
        self.get_step_mut(step, ptcl)?.msg = msg;
        Ok(())
    }

    fn set_step_cond(&self, step: Function, ptcl: Function, cond: RecFOFormula) -> SResult<()> {
        self.get_step_mut(step, ptcl)?.cond = cond;
        Ok(())
    }

    fn add_rule(&self, Rule(r): Rule) {
        self.borrow_mut().extra_rules_mut().push(r);
    }

    fn add_rewrite(&self, rw: Rewrite) {
        self.borrow_mut().extra_rewrite_mut().push(rw);
    }

    fn add_smt_axiom(&self, f: RecFOFormula) -> SResult<()> {
        self.borrow_mut().extra_smt_mut().push(MSmt::mk_assert(
            f.as_smt(self.0.borrow().deref())
                .ok_or(conversion_err::<MSmt>())?,
        ));
        Ok(())
    }

    // =========================================================
    // ====================== printing =========================
    // =========================================================

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

impl Registerable for ShrProblem {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module);
        module
            .register_fn("to-string-step", Self::to_string_step)
            .register_fn("empty-problem", Self::mk_empty)
            .register_fn("declare-function", Self::declare_function)
            .register_fn("declare-protocol", Self::declare_protocol)
            .register_fn("declare-exists", Self::declare_exists)
            .register_fn("declare-find-such-that", Self::declare_fdst)
            .register_fn("declare-step", Self::declare_step)
            .register_fn("set-step-message", Self::set_step_msg)
            .register_fn("set-step-condition", Self::set_step_cond)
            .register_fn("set-step-vars", Self::set_step_vars)
            .register_fn("get-step-variables", Self::get_step_vars)
            .register_fn("add-rule", Self::add_rule)
            .register_fn("add-rewrite", Self::add_rewrite)
            .register_fn("add-smt-axiom", Self::add_smt_axiom)
            .register_fn("run", Self::run);

        module
    }
}
