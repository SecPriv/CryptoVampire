use std::fmt::Display;

use anyhow::{bail, ensure};
use bon::{bon, builder};
use egg::{Analysis, Pattern, Rewrite};
use itertools::{Itertools, chain, izip};
use log::trace;
use logic_formula::AsFormula;
use logic_formula::iterators::AllTermsIterator;
use rustc_hash::{FxHashMap, FxHashSet};
use steel::rerrs::ErrorKind;
use steel_derive::Steel;
use thiserror::Error;
use utils::implvec;

use crate::input::Registerable;
use crate::libraries::utils::{EggRewriteSink, INDEPEDANT_QUERY, SmtSink};
use crate::protocol::SingleAssignement;
use crate::protocol::memory_cell::Assignements;
use crate::terms::{EMPTY, Formula, Function, INIT, Sort, UNFOLD_COND, UNFOLD_MSG, Variable};
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
    pub fn freshen(&self) -> Self {
        let Self {
            id,
            vars,
            cond,
            msg,
            assignements,
        } = self;
        let nvars = vars.iter().map(Variable::freshen).collect_vec();
        let mut subst: FxHashMap<_, _> = izip!(vars.iter(), nvars.iter().cloned()).collect();
        trace!("Step::freshen: {} -> {:?}", id, nvars);

        let cond = cond.apply_substitution(&mut subst);
        let msg = msg.apply_substitution(&mut subst);
        let assignements = assignements
            .iter()
            .map(|(k, v)| (k.clone(), v.freshen(&mut subst)))
            .collect();
        let res = Self {
            id: id.clone(),
            vars: nvars,
            cond,
            msg,
            assignements,
        };

        #[cfg(debug_assertions)]
        {
            res.is_valid().unwrap();
        }

        res
    }

    /// Returns the expression of the step id with its variables
    pub fn id_expr(&self) -> Formula {
        let Self { id, vars, .. } = self;
        rexp!((id #(vars.iter().map_into())*))
    }

    /// Checks if the step is valid
    pub fn is_valid(&self) -> anyhow::Result<()> {
        let Self {
            vars, cond, msg, ..
        } = self;

        ensure!(self.id.is_step(), "{} is not marked as a step", self.id);

        ensure!(
            self.id.signature.output == Sort::Time,
            "{} should output sort 'Time' (got {})",
            self.id,
            self.id.signature.output
        );

        for v in chain![cond.free_vars_iter(), msg.free_vars_iter()] {
            ensure!(
                vars.contains(v),
                "{v} should be bound in the arguments {}",
                self.id
            )
        }

        let mut vars: FxHashSet<_> = Default::default();
        for (
            id,
            SingleAssignement {
                assignement_vars,
                parameter_vars,
                value,
            },
        ) in &self.assignements
        {
            ensure!(
                id.is_memory_cell(),
                "'{}' is not registered as a memory cell (in {})",
                id,
                self.id
            );
            ensure!(
                id.signature.output == Sort::MemoryCell,
                "'{}' shoud output 'MemoryCell' (got {}, in {})",
                id,
                id.signature.output,
                self.id
            );

            vars.clear();
            vars.reserve(parameter_vars.len() + self.vars.len());
            vars.extend(self.vars.iter());
            for v in parameter_vars {
                ensure!(
                    vars.insert(v),
                    "{v} shadows a variable bound by {} (in {}'s definition)",
                    self.id,
                    id
                );
            }

            for v in chain![assignement_vars.iter(), value.free_vars_iter()] {
                ensure!(
                    vars.contains(v),
                    "{v} is free (in {}'s definition in step {})",
                    id,
                    self.id
                )
            }
        }

        Ok(())
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
        sink: &mut impl EggRewriteSink<N>,
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
    pub(crate) fn add_unfold_vampire_rewrites<'a>(
        &self,
        pbl: &Problem,
        ptcl: &MSmtFormula<'a>,
        sink: &mut impl SmtSink<'a>,
    ) {
        let [cond, msg, name]: [MSmtFormula<'a>; _] =
            [&self.cond, &self.msg, &self.id_expr()].map(|x| x.as_smt(pbl).unwrap());
        let vars = self.vars.iter().cloned();

        sink.extend_smt(
            pbl,
            &INDEPEDANT_QUERY,
            vec_smt![%
                ; format!("unfolding of {name}"),
                (forall !(vars.clone()) (= (UNFOLD_COND #name #ptcl) #cond)),
                (forall !(vars.clone()) (= (UNFOLD_MSG #name #ptcl) #msg))
            ],
        )
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
pub(crate) enum InvalidStepError {
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
    #[error("{msg}")]
    #[allow(unused)]
    Other { msg: String },
}

impl From<InvalidStepError> for steel::rerrs::SteelErr {
    fn from(value: InvalidStepError) -> Self {
        let kind = match &value {
            InvalidStepError::WrongProtocol { .. } | InvalidStepError::Other { .. } => {
                ErrorKind::Generic
            }
            InvalidStepError::FreeVariable { .. } => ErrorKind::FreeIdentifier,
        };
        Self::new(kind, value.to_string())
    }
}

pub(crate) fn check_elem<'a, I, II>(
    pbl: &Problem,
    step: &Function,
    ptcl: &Function,
    elem: &Formula,
    extra_vars: I,
) -> Result<(), InvalidStepError>
where
    I: IntoIterator<IntoIter = II>,
    II: Iterator<Item = &'a Variable> + Clone,
{
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
    #[allow(clippy::map_identity, reason = "liftime magic")]
    let vars = chain![vars.iter(), extra_vars.into_iter().map(|v| v)];
    for v in elem.free_vars_iter() {
        if !vars.clone().contains(&v) {
            return Err(InvalidStepError::FreeVariable {
                var: v.clone(),
                formula: elem.clone(),
            });
        }
    }

    Ok(())
}

mod msteel {
    use itertools::chain;
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
    use crate::protocol::SingleAssignement;
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
        check_elem(&pbl.borrow(), &step, &ptcl, &msg, [])?;
        pbl.get_step_mut(step, ptcl)?.msg = msg;
        Ok(())
    }

    /// Sets the condition for a given step in a protocol.
    #[steel_derive::declare_steel_function(name = "set-cond")]
    fn set_cond(pbl: ShrProblem, step: Function, ptcl: Function, cond: Formula) -> SResult<()> {
        check_elem(&pbl.borrow(), &step, &ptcl, &cond, [])?;
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

            let module = modules
                .entry(name.into())
                .or_insert_with(|| BuiltInModule::new(name));

            Self::register_type(module);
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

            trace!("defined {name} for steps scheme module");
        }
    }
}

#[cfg(test)]
pub mod test {}
