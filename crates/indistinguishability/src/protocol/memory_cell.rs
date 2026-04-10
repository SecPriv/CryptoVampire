use anyhow::ensure;
use bon::{Builder, bon, builder};
use itertools::{Itertools, chain, izip};
use logic_formula::AsFormula;
use rustc_hash::{FxHashMap, FxHashSet};
use steel_derive::Steel;

use crate::rexp;
use crate::terms::{Formula, Function, INDEX_EQ, MACRO_MEMORY_CELL, MITE, PRED, Sort, Variable};
// TODO:
// - rewrite rules for state
// deal with unassigned state
// init
// - subterm
// traditionnal before a `pred`
// depency listing

#[derive(Debug, Clone, PartialEq, Eq, Hash, Builder)]
pub struct MemoryCell {
    function: Function,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Steel)]
pub struct SingleAssignement {
    /// The variables used in the assignement definition
    pub assignement_vars: Vec<Variable>,
    /// The variables used as parameters for the cell
    pub parameter_vars: Vec<Variable>,
    pub(crate) value: Formula,
}

pub type Assignements = FxHashMap<Function, SingleAssignement>;

#[bon]
impl SingleAssignement {
    #[builder]
    pub fn new(
        #[builder(with = <_>::from_iter, default = vec![])] assignement_vars: Vec<Variable>,
        #[builder(with = <_>::from_iter, default = vec![])] parameter_vars: Vec<Variable>,
        value: Formula,
    ) -> anyhow::Result<Self> {
        // Check sort first (uses reference, doesn't move)
        ensure!(
            value.has_sort(Sort::Bitstring),
            "the content of a state should have sort `Bitstring`"
        );

        // Check free vars (use reference to avoid moving value)
        let free_vars: FxHashSet<_> = chain![&assignement_vars, &parameter_vars].collect();
        ensure!(
            (&value).free_vars_iter().all(|v| free_vars.contains(v)),
            "free varaible"
        );

        Ok(Self {
            assignement_vars,
            parameter_vars,
            value,
        })
    }
}

impl SingleAssignement {
    /// $c(\vec\jmath)@\tau := \textbf{if }\vec\jmath = \vec\imath \textbf{ then } m \textbf{ else } c(\vec\jmath)@\mathrm{pred}(\tau)$
    ///
    /// `c(ȷ⃗)@τ := if ȷ⃗ = ı⃗ then  m else  c(ȷ⃗)@pred(τ)`
    pub fn mk_formula(&self, fun: &Function, tau: &Formula, ptcl: &Formula) -> Formula {
        let Self {
            assignement_vars,
            parameter_vars,
            value,
        } = self;
        debug_assert!(
            fun.args_sorts()
                .eq(parameter_vars.iter().flat_map(Variable::get_sort))
        );
        debug_assert!(
            fun.args_sorts()
                .eq(assignement_vars.iter().flat_map(Variable::get_sort))
        );

        let js = parameter_vars.iter().cloned().map(Formula::Var);
        let is = assignement_vars.iter().cloned().map(Formula::Var);
        let id_eq = izip!(js.clone(), is).map(|(j, i)| rexp!((INDEX_EQ #j #i)));

        rexp!((MITE (and #id_eq*) #value (MACRO_MEMORY_CELL (fun #js*) (PRED #tau) #ptcl)))
    }

    pub fn mk_default_formula(
        fun: &Function,
        tau: &Formula,
        ptcl: &Formula,
    ) -> (Vec<Variable>, Formula) {
        let vars = fun.args_vars().collect_vec();
        let vars_iters = vars.iter().cloned().map(Formula::Var);
        let formula = rexp!((MACRO_MEMORY_CELL (fun #vars_iters*) (PRED #tau) #ptcl));
        (vars, formula)
    }

    pub fn value(&self) -> &Formula {
        &self.value
    }
}

impl MemoryCell {
    pub fn function(&self) -> &Function {
        &self.function
    }
}

mod steel {
    use itertools::chain;
    use log::trace;
    use logic_formula::AsFormula;
    use logic_formula::iterators::AllTermsIterator;
    use steel::rerrs::ErrorKind;
    use steel::rvals::{IntoSteelVal, Result as SResult};
    use steel::steel_vm::builtin::BuiltInModule;
    use steel::{SteelErr, SteelVal};

    use crate::input::Registerable;
    use crate::input::shared_problem::ShrProblem;
    use crate::protocol::step::check_elem;
    use crate::protocol::{MemoryCell, SingleAssignement};
    use crate::terms::{Formula, Function, Sort, Variable};

    #[steel_derive::declare_steel_function(name = "mk-single-assignment")]
    fn mk_single_assignement(
        assignement_vars: Vec<Variable>,
        parameter_vars: Vec<Variable>,
        value: Formula,
    ) -> SResult<SteelVal> {
        let sa = SingleAssignement::builder()
            .assignement_vars(assignement_vars)
            .parameter_vars(parameter_vars)
            .value(value)
            .build();
        match sa {
            Err(e) => Err(SteelErr::new(ErrorKind::Generic, e.to_string())),
            Ok(s) => Ok(s.into_steelval()?),
        }
    }

    /// Sets an assignment for a memory cell at a given step.
    #[steel_derive::declare_steel_function(name = "insert-assignement")]
    fn set_assignment(
        pbl: ShrProblem,
        step: Function,
        ptcl: Function,
        cell: Function,
        assignement: SingleAssignement,
    ) -> SResult<()> {
        {
            let SingleAssignement {
                assignement_vars,
                parameter_vars,
                value,
            } = &assignement;
            check_elem(
                &pbl.borrow(),
                &step,
                &ptcl,
                value,
                chain![assignement_vars, parameter_vars],
            )?;
        }

        if !ptcl.is_protocol() {
            return Err(SteelErr::new(
                ErrorKind::TypeMismatch,
                "'ptcl' should be Protocol".to_string(),
            ));
        }

        if !step.is_step() {
            return Err(SteelErr::new(
                ErrorKind::TypeMismatch,
                "'step' should be a step".to_string(),
            ));
        }

        if !cell.is_memory_cell() {
            return Err(SteelErr::new(
                ErrorKind::TypeMismatch,
                "'step' should be a cell".to_string(),
            ));
        }

        pbl.get_step_mut(step, ptcl)?
            .assignements
            .insert(cell, assignement);
        Ok(())
    }

    impl Registerable for MemoryCell {
        fn register(modules: &mut rustc_hash::FxHashMap<String, BuiltInModule>) {
            let name = "cryptovampire/ll/step";

            let module = modules
                .entry(name.into())
                .or_insert_with(|| BuiltInModule::new(name));
            SingleAssignement::register_type(module);
            module
                .register_type::<SingleAssignement>("SingleAssignement?")
                .register_native_fn_definition(SET_ASSIGNMENT_DEFINITION)
                .register_native_fn_definition(MK_SINGLE_ASSIGNEMENT_DEFINITION);
            trace!("defined {name} for memory cells scheme module");
        }
    }
}
