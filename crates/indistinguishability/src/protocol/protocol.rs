use std::fmt::Display;
use std::ops::Index;

use anyhow::{bail, ensure};
use bon::Builder;
use itertools::{Itertools, izip};
use rustc_hash::FxHashMap;
use utils::{ereturn_if, ereturn_let};

use super::Step;
use crate::protocol::call_graph::{Graph, StepRef};
use crate::terms::{Formula, Function, INIT, Sort};
use crate::{MSmtFormula, Problem, rexp, smt};
/// A protocol to be proven
#[derive(Debug, Clone, Builder)]
pub struct Protocol {
    /// The name of the protocol
    name: Function,
    /// The steps of the protocol
    #[builder(with = <_>::from_iter, default = vec![Step::default()])]
    steps: Vec<Step>,

    #[builder(default)]
    graph: Graph,
}

impl Protocol {
    /// Creates a new protocol with the given name
    pub fn new(name: Function) -> Self {
        Self::builder().name(name).build()
    }

    /// Two protocols are compatible if they have the same step names
    pub fn are_compatible(
        Protocol { steps: steps_a, .. }: &Protocol,
        Protocol { steps: steps_b, .. }: &Protocol,
    ) -> bool {
        let mut steps_a = steps_a.iter().map(|s| &s.id).collect_vec();
        let mut steps_b = steps_b.iter().map(|s| &s.id).collect_vec();
        steps_a.sort_unstable();
        steps_b.sort_unstable();
        steps_a == steps_b
    }

    /// Returns the steps of the protocol
    #[inline]
    pub fn steps(&self) -> &[Step] {
        &self.steps
    }

    /// Returns the name of the protocol
    #[inline]
    pub fn name(&self) -> &Function {
        &self.name
    }

    /// Converts the protocol's name into an SMT formula.
    pub(crate) fn as_smt<'a>(&self) -> MSmtFormula<'a> {
        let name = self.name();
        smt!(name)
    }

    /// Adds a new step to the protocol.
    ///
    /// # Panics
    ///
    /// Panics if the provided step is not valid (i.e., its free variables are not contained in its step variables).
    pub(crate) fn add_step(&mut self, step: Step) -> &mut Step {
        step.is_valid().unwrap();

        self.graph.clear();
        self.steps.push(step);
        self.steps.last_mut().unwrap()
    }

    /// Returns a mutable reference to the step at the given index
    pub fn step_mut(&mut self, idx: usize) -> Option<&mut Step> {
        self.graph.clear();
        self.steps.get_mut(idx)
    }

    pub(crate) fn truncate_steps(&mut self, n: usize) {
        self.graph.clear();
        self.steps.truncate(n);
    }

    pub fn graph(&self) -> Option<&Graph> {
        ereturn_if!(self.graph.is_initialized(), None);
        Some(&self.graph)
    }

    pub(crate) fn graph_mut(&mut self) -> &mut Graph {
        &mut self.graph
    }

    pub fn get_step_from_ref(&self, StepRef(idx): StepRef) -> Option<&Step> {
        self.steps().get(idx)
    }

    pub fn from_formula<'a>(pbl: &'a Problem, f: &Formula) -> Option<&'a Self> {
        if let Formula::App { head, args } = f
            && args.is_empty()
            && let Some(idx) = head.get_protocol_index()
            && let Some(ptcl) = pbl.protocols().get(idx)
        {
            Some(ptcl)
        } else {
            None
        }
    }

    pub fn is_valid(&self, pbl: &Problem) -> anyhow::Result<()> {
        let sign = &self.name.signature;
        ensure!(
            self.name.is_protocol(),
            "{self} isn't fully registered as a protocol"
        );
        ensure!(
            sign.arity() == 0,
            "{self} should not have parameters (got arity {:})",
            sign.arity()
        );
        ensure!(
            sign.output == Sort::Protocol,
            "{self}'s name should have sort 'Protocol' (got {})",
            sign.output
        );
        if let Some(init) = self.steps().first()
            && init.id == INIT
        {
        } else {
            bail!("no init step or not in first position in {self}")
        }

        for s in self.steps() {
            s.is_valid()?;

            if s.id == INIT {
                for c in pbl.functions().memory_cells() {
                    ensure!(
                        s.assignements.contains_key(c),
                        "{c} should have a default value in {INIT}"
                    )
                }
            }
        }
        Ok(())
    }
}

impl PartialEq for Protocol {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.steps == other.steps
    }
}

impl Eq for Protocol {}

mod converter {
    use rustc_hash::FxHashMap;

    use crate::rexp;
    use crate::terms::{Formula, Function, Variable};

    // FIXME: what was this used for ?
    pub(crate) fn clone_from_sanitizer(
        subst: &mut FxHashMap<Variable, Variable>,
        from: &Function,
        to: &Formula,
        into: &Formula,
    ) -> Formula {
        match into {
            Formula::Quantifier { head, vars, arg } => {
                let vars = vars
                    .iter()
                    .map(|v| (v, v.freshen()))
                    .inspect(|(v, nv)| assert!(subst.insert((*v).clone(), nv.clone()).is_none()))
                    .map(|(_, v)| v)
                    .collect();
                let arg = arg.iter().map(|x| clone_from_sanitizer(subst, from, to, x));
                Formula::Quantifier {
                    head: *head,
                    vars,
                    arg: arg.collect(),
                }
            }
            Formula::App { head, .. } if head == from => to.clone(),
            Formula::App { head, args } => {
                let args = args
                    .iter()
                    .map(|x| clone_from_sanitizer(subst, from, to, x));
                rexp!((head #args*))
            }
            Formula::Var(variable) => {
                let var = subst
                    .get(variable)
                    .expect("there cannot be free variables")
                    .clone();
                Formula::Var(var)
            }
        }
    }
}

impl Index<StepRef> for Protocol {
    type Output = Step;

    fn index(&self, index: StepRef) -> &Self::Output {
        self.get_step_from_ref(index).unwrap()
    }
}

impl Display for Protocol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}
