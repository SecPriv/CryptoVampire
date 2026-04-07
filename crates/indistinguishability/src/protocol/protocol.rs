use bon::Builder;
use itertools::{Itertools, izip};
use rustc_hash::FxHashMap;

use super::Step;
use crate::terms::{Formula, Function};
use crate::{MSmtFormula, rexp, smt};
/// A protocol to be proven
#[derive(Debug, PartialEq, Eq, Clone, Builder)]
pub struct Protocol {
    /// The name of the protocol
    name: Function,
    /// The steps of the protocol
    #[builder(with = <_>::from_iter, default = vec![Step::default()])]
    steps: Vec<Step>,
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

    pub(crate) fn as_formula(&self) -> Formula {
        let name = self.name();
        rexp!(name)
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
        assert!(step.valid());
        self.steps.push(step);
        self.steps.last_mut().unwrap()
    }

    /// Returns a mutable reference to the step at the given index
    pub fn step_mut(&mut self, idx: usize) -> Option<&mut Step> {
        self.steps.get_mut(idx)
    }

    pub(crate) fn truncate_steps(&mut self, n: usize) {
        self.steps.truncate(n);
    }

    pub fn clone_from(&mut self, other: &Self) {
        let Self { name: _, steps } = self;

        let mut varmap = FxHashMap::default();
        for (sl, sr) in izip!(steps, &other.steps) {
            let nvars = sr.vars.iter().map(|v| v.freshen()).collect_vec();
            varmap.clear();
            varmap.extend(izip!(sr.vars.iter().cloned(), nvars.iter().cloned()));
            let to = other.name.rapp([]);
            let msg = converter::clone_from_sanitizer(&mut varmap, &self.name, &to, &sr.cond);
            let cond = converter::clone_from_sanitizer(&mut varmap, &self.name, &to, &sr.msg);
            sl.vars = nvars;
            sl.msg = msg;
            sl.cond = cond;
        }
    }
}

mod converter {
    use rustc_hash::FxHashMap;

    use crate::rexp;
    use crate::terms::{Formula, Function, Variable};

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
