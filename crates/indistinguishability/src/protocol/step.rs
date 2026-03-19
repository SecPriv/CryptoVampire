use std::fmt::Display;

use bon::bon;
use cryptovampire_smt::SmtSink;
use egg::{Analysis, Pattern, Rewrite};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::AsFormula;
use logic_formula::iterators::AllTermsIterator;
use steel::rerrs::ErrorKind;
use steel_derive::Steel;
use thiserror::Error;

use crate::input::Registerable;
use crate::libraries::utils::EggRewriteSink;
use crate::protocol::memory_cell::Assignements;
use crate::terms::{EMPTY, Formula, Function, INIT, UNFOLD_COND, UNFOLD_MSG, Variable};
use crate::{Lang, MSmt, MSmtFormula, MSmtParam, Problem, rexp, vec_smt};

bitflags::bitflags! {
  #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
           Hash, Debug)]
  pub struct StepFlags: u8 {
      /// The function is builtin
      const PUBLICATION = 1 << 0;
  }
}

/// A step in protocol
#[derive(Debug, PartialEq, Eq, Clone, Steel)]
// #[steel(getters, constructors)]
pub struct Step {
    /// The identifier of the step
    pub id: Function,
    /// The variables of the step
    pub vars: Vec<Variable>,
    /// The condition of the step
    pub cond: Formula,
    /// The message of the step
    pub msg: Formula,
    pub assignements: Assignements,
}

impl Default for Step {
    fn default() -> Self {
        Step::builder().build().unwrap()
    }
}

#[bon]
impl Step {
    /// Creates a new step
    ///
    /// Returns `None` if the number of variables is different from the arity of the step id.
    #[builder]
    pub fn new(
        #[builder(default = INIT.clone())] id: Function,
        #[builder(with = <_>::from_iter, default = vec![])] vars: Vec<Variable>,
        #[builder(default = Formula::True())] cond: Formula,
        #[builder(default = Formula::constant(EMPTY.clone()))] msg: Formula,
        #[builder(default)] assignements: Assignements,
    ) -> Option<Step> {
        (vars.len() == id.signature.arity()).then_some(())?;
        Some(Self {
            id,
            vars,
            cond,
            msg,
            assignements,
        })
    }
}

impl Step {
    /// Returns the expression of the step id with its variables
    pub fn id_expr(&self) -> Formula {
        let Self { id, vars, .. } = self;
        rexp!((id #(vars.iter().map_into())*))
    }

    /// Checks if the step is valid
    ///
    /// A step is valid if all the free variables in the condition and the message
    /// are contained in the step variables.
    pub fn valid(&self) -> bool {
        let Self {
            vars, cond, msg, ..
        } = self;

        chain![cond.free_vars_iter(), msg.free_vars_iter()].all(|v| vars.contains(v))
    }
}

impl Display for Step {
    /// Formats the `Step` for display.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            id,
            vars,
            cond,
            msg,
            ..
        } = self;
        write!(
            f,
            "step {id}({}):\n\tcond: {cond}\n\tmsg: {msg}",
            vars.iter().join(", ")
        )
    }
}

impl Step {
    /// Creates an iterator of `Rewrite` rules for unfolding the condition and message of this step.
    ///
    /// These rewrites are used in the e-graph to replace `UNFOLD_COND` and `UNFOLD_MSG` applications
    /// with the actual condition and message formulas of the step.
    pub(crate) fn add_unfold_rewrites<N: Analysis<Lang>>(
        &self,
        ptcl: &Function,
        sink: &mut impl EggRewriteSink<N>
    ) {
        trace!("mk unfold rw for {self}");
        let name = &self.id_expr();
        let ptcl = &rexp!(ptcl);

        let unfold_cond = Rewrite::new(
            format!("unfold cond {name} in {ptcl}"),
            Pattern::from(&rexp!((UNFOLD_COND #name #ptcl))),
            Pattern::from(&self.cond),
        )
        .unwrap();
        let unfold_msg = Rewrite::new(
            format!("unfold msg {name} in {ptcl}"),
            Pattern::from(&rexp!((UNFOLD_MSG #name #ptcl))),
            Pattern::from(&self.msg),
        )
        .unwrap();

        sink.extend_egg_rewrites([unfold_cond, unfold_msg])
    }

    /// Creates an iterator of SMT formulas representing the unfolding of the condition and message
    /// for use with the Vampire SMT solver.
    pub(crate) fn add_unfold_vampire_rewrites(
        &self,
        pbl: &Problem,
        ptcl: &MSmtFormula,
        sink: &mut impl SmtSink<MSmtParam>
    ){
        let [cond, msg, name]: [MSmtFormula; _] =
            [&self.cond, &self.msg, &self.id_expr()].map(|x| x.as_smt(pbl).unwrap());
        let vars = self.vars.iter().cloned();

        sink.extend_smt(vec_smt![%
            ; format!("unfolding of {name}"),
            (forall !(vars.clone()) (= (UNFOLD_COND #name #ptcl) #cond)),
            (forall !(vars.clone()) (= (UNFOLD_MSG #name #ptcl) #msg))
        ])
    }

    pub fn mk_publish_step(id: Function, msg: Formula) -> Self {
        Self {
            id,
            vars: Vec::new(),
            cond: rexp!(true),
            msg,
            assignements: Default::default(),
        }
    }
}

#[derive(Debug, Clone, Error)]
enum InvalidStepError {
    #[error(
        "wrong protocol referenced (expected only references to {expected} got {got}) \
         in\n\t{formula}"
    )]
    WrongProtocol {
        expected: Function,
        got: Function,
        formula: Formula,
    },
    #[error("Variable {var} is free in\n\t{formula}")]
    FreeVariable { var: Variable, formula: Formula },
}

impl From<InvalidStepError> for steel::rerrs::SteelErr {
    fn from(value: InvalidStepError) -> Self {
        let kind = match &value {
            InvalidStepError::WrongProtocol { .. } => ErrorKind::Generic,
            InvalidStepError::FreeVariable { .. } => ErrorKind::FreeIdentifier,
        };
        Self::new(kind, value.to_string())
    }
}

fn check_elem(
    pbl: &Problem,
    step: &Function,
    ptcl: &Function,
    elem: &Formula,
) -> Result<(), InvalidStepError> {
    for f in elem.iter_with(AllTermsIterator, ()) {
        if let Formula::App { head, .. } = f
            && head.is_protocol()
            && head != ptcl
        {
            return Err(InvalidStepError::WrongProtocol {
                expected: ptcl.clone(),
                got: head.clone(),
                formula: elem.clone(),
            });
        }
    }

    let vars = &pbl.protocols()[ptcl.protocol_idx].steps()[step.step_idx].vars;
    for v in elem.free_vars_iter() {
        if !vars.contains(v) {
            return Err(InvalidStepError::FreeVariable {
                var: v.clone(),
                formula: elem.clone(),
            });
        }
    }

    Ok(())
}

mod msteel {
    use log::trace;
    use logic_formula::AsFormula;
    use logic_formula::iterators::AllTermsIterator;
    use steel::rerrs::ErrorKind;
    use steel::rvals::{IntoSteelVal, Result as SResult};
    use steel::steel_vm::builtin::BuiltInModule;
    use steel::{SteelErr, SteelVal};

    use super::Step;
    use crate::input::Registerable;
    use crate::input::shared_problem::ShrProblem;
    use crate::protocol::step::check_elem;
    use crate::terms::{Formula, Function, Sort, Variable};

    /// Sets the variables for a given step in a protocol.
    #[steel_derive::declare_steel_function(name = "declare-exists")]
    fn set_vars(
        pbl: ShrProblem,
        step: Function,
        ptcl: Function,
        vars: Vec<Variable>,
    ) -> SResult<()> {
        let mut step = pbl.get_step_mut(step, ptcl)?;

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
    #[steel_derive::declare_steel_function(name = "get-vars")]
    fn get_vars(pbl: ShrProblem, step: Function, ptcl: Function) -> SResult<SteelVal> {
        pbl.get_step_mut(step, ptcl)?.vars.clone().into_steelval()
    }

    /// Sets the message for a given step in a protocol.
    #[steel_derive::declare_steel_function(name = "set-msg")]
    fn set_msg(pbl: ShrProblem, step: Function, ptcl: Function, msg: Formula) -> SResult<()> {
        check_elem(&pbl.borrow(), &step, &ptcl, &msg)?;
        pbl.get_step_mut(step, ptcl)?.msg = msg;
        Ok(())
    }

    /// Sets the condition for a given step in a protocol.
    #[steel_derive::declare_steel_function(name = "set-cond")]
    fn set_cond(pbl: ShrProblem, step: Function, ptcl: Function, cond: Formula) -> SResult<()> {
        check_elem(&pbl.borrow(), &step, &ptcl, &cond)?;
        pbl.get_step_mut(step, ptcl)?.cond = cond;
        Ok(())
    }

    /// Sets the message for a given step in a protocol.
    #[steel_derive::declare_steel_function(name = "get-msg")]
    fn get_msg(pbl: ShrProblem, step: Function, ptcl: Function) -> SResult<SteelVal> {
        pbl.get_step_mut(step, ptcl)?.msg.clone().into_steelval()
    }

    /// Sets the condition for a given step in a protocol.
    #[steel_derive::declare_steel_function(name = "get-cond")]
    fn get_cond(pbl: ShrProblem, step: Function, ptcl: Function) -> SResult<SteelVal> {
        pbl.get_step_mut(step, ptcl)?.cond.clone().into_steelval()
    }

    /// Declares a new step function in the problem.
    #[steel_derive::declare_steel_function(name = "declare-step")]
    fn declare(pbl: ShrProblem, name: String, sorts: Vec<Sort>) -> SResult<SteelVal> {
        match pbl.borrow_mut().declare_step(name, sorts) {
            Err(e) => Err(SteelErr::new(ErrorKind::Generic, e.to_string())),
            Ok(s) => Ok(s.into_steelval()?),
        }
    }

    // =========================================================
    // ====================== printing =========================
    // =========================================================

    /// Returns a string representation of a specific step in a protocol.
    #[steel_derive::declare_steel_function(name = "string")]
    fn to_string(pbl: ShrProblem, ptcl: Function, step: Function) -> SResult<SteelVal> {
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

        let pbl = pbl.borrow();
        let step = &pbl.protocols()[pidx].steps()[sidx];
        format!("{step}").into_steelval()
    }

    impl Registerable for Step {
        fn register(modules: &mut rustc_hash::FxHashMap<String, BuiltInModule>) {
            let name = "cryptovampire/ll/step";
            let mut module = BuiltInModule::new(name);
            Self::register_type(&mut module);
            module
                .register_type::<Self>("Step?")
                .register_native_fn_definition(TO_STRING_DEFINITION)
                .register_native_fn_definition(SET_VARS_DEFINITION)
                .register_native_fn_definition(SET_COND_DEFINITION)
                .register_native_fn_definition(SET_MSG_DEFINITION)
                .register_native_fn_definition(GET_VARS_DEFINITION)
                .register_native_fn_definition(GET_COND_DEFINITION)
                .register_native_fn_definition(GET_MSG_DEFINITION)
                .register_native_fn_definition(DECLARE_DEFINITION)
                .register_native_fn_definition(TO_STRING_DEFINITION);

            trace!("defined {name} scheme module");
            assert!(modules.insert(name.into(), module).is_none())
        }
    }
}

#[cfg(test)]
pub mod test {}
