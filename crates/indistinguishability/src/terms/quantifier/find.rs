use std::collections::HashSet;
use std::fmt::Display;
use std::rc::Rc;

use bon::{Builder, bon};
use itertools::{Itertools, chain};
use logic_formula::AsFormula;
use utils::ereturn_if;

use crate::Problem;
use crate::terms::quantifier::default_valid;
use crate::terms::{
    Formula, Function, FunctionFlags, Quantifier, QuantifierIndex, QuantifierT, Sort, Variable,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Builder)]
#[builder(builder_type = FindSuchThatBuilder0)]
pub struct FindSuchThat {
    /// The free variables captured by the quantifier
    #[builder(with = <_>::from_iter)]
    vars: Vec<Variable>,
    /// The variable bound by the quantifier
    #[builder(with = <_>::from_iter)]
    bound_var: Vec<Variable>,
    #[builder(default = true)]
    temporary: bool,
    /// The "content" of the quantifier
    condition: Option<Formula>,
    then_branch: Option<Formula>,
    else_branch: Option<Formula>,
    /// the main alias (e.g., `exists$1`)
    ///
    /// stands for "top level function"
    tlf: Function,
    /// the skolem function
    skolems: Vec<Function>,
    /// the fresh constant replacing the index
    freshes: Vec<Function>,
}

impl QuantifierT for FindSuchThat {
    fn bvars(&self) -> &[Variable] {
        &self.bound_var
    }

    fn cvars(&self) -> &[Variable] {
        &self.vars
    }

    fn top_level_function(&self) -> &Function {
        &self.tlf
    }

    fn skolems(&self) -> &[Function] {
        &self.skolems
    }

    fn fresh_indices(&self) -> &[Function] {
        &self.freshes
    }

    fn valid(&self, idx: QuantifierIndex, pbl: &crate::Problem) -> bool {
        ereturn_if!(!default_valid(self, idx, pbl), false);

        let mut all_vars_set = HashSet::with_capacity(self.bvars().len() + self.cvars().len());
        for v in chain![self.bvars(), self.cvars()] {
            ereturn_if!(all_vars_set.insert(v), false)
        }
        let all_vars_set = all_vars_set;

        let patterns_vars: HashSet<_> = [self.condition(), self.then_branch(), self.else_branch()]
            .into_iter()
            .flatten()
            .flat_map(|x| x.free_vars_iter())
            .collect();

        all_vars_set.is_superset(&patterns_vars)
    }

    fn try_from_ref(q: &super::Quantifier) -> Option<&Self> {
        match q {
            super::Quantifier::FindSuchThat(exists) => Some(exists),
            _ => None,
        }
    }

    fn try_from_mut(q: &mut super::Quantifier) -> Option<&mut Self> {
        match q {
            super::Quantifier::FindSuchThat(exists) => Some(exists),
            _ => None,
        }
    }

    fn temporary(&self) -> bool {
        self.temporary
    }
}

#[bon]
impl FindSuchThat {
    /// The returned [Exists] has it's [Exists::vars], [Exists::bound_var] and
    /// [Exists::patt] left empty.
    #[builder]
    pub fn insert(
        pbl: &mut Problem,
        #[builder(with = FromIterator::from_iter, default = vec![])] cvars: Vec<Variable>,
        #[builder(with = FromIterator::from_iter, default = vec![])] bvars: Vec<Variable>,
        #[builder(default = true)] temporary: bool,
    ) -> &mut FindSuchThat {
        assert!(!bvars.is_empty());
        let bvars_sorts = bvars
            .iter()
            .map(|v| {
                v.get_sort()
                    .expect("quantifiers should capture variables with sort")
            })
            .collect_vec();
        let cvars_sorts = cvars
            .iter()
            .map(|v| {
                v.get_sort()
                    .expect("quantified variables should have a sort")
            })
            .collect_vec();

        debug_assert!(
            bvars.iter().all(|v| !cvars.contains(v)),
            "bound vars in captured vars!"
        );
        debug_assert!(
            cvars.iter().all(|v| !bvars.contains(v)),
            "captured vars in bound vars!"
        );
        debug_assert!(bvars.iter().all_unique(), "bvars must be unique");
        debug_assert!(cvars.iter().all_unique(), "cvars must be unique");

        let quant_idx = pbl.functions().quantifiers(temporary).len();

        // let n_quant = QUANTIFIER_COUNT.fetch_add(1, std::sync::atomic::Ordering::AcqRel);

        // build the Functions
        let tlf;
        let skolems;
        let freshes;

        {
            tlf = pbl
                .declare_function()
                .fresh_name("_findst")
                .inputs(chain!(cvars_sorts.clone(), bvars_sorts.clone()))
                .output(Sort::Bitstring)
                .quantifier_idx(quant_idx)
                .flag(FunctionFlags::FIND_SUCH_THAT)
                .set_temporary(temporary)
                .call()
        }

        {
            // skolem
            let mut skolem_vec = Vec::with_capacity(bvars_sorts.len());
            let name = format!("_sk${}", tlf.name);
            for &bs in &bvars_sorts {
                skolem_vec.push(
                    pbl.declare_function()
                        .fresh_name(&name)
                        .inputs(cvars_sorts.clone())
                        .output(bs)
                        .quantifier_idx(quant_idx)
                        .flag(FunctionFlags::SKOLEM)
                        .set_temporary(temporary)
                        .call(),
                );
            }
            skolems = skolem_vec;
        }

        {
            // fresh
            let mut fresh_vec = Vec::with_capacity(bvars_sorts.len());
            let name = format!("_fresh${}", tlf.name);
            for &bs in &bvars_sorts {
                fresh_vec.push(
                    pbl.declare_function()
                        .fresh_name(&name)
                        .output(bs)
                        .quantifier_idx(quant_idx)
                        .flag(FunctionFlags::QUANTIFIER_FRESH)
                        .set_temporary(temporary)
                        .call(),
                );
            }
            freshes = fresh_vec;
        }

        let q = pbl.functions_mut().push_quantifier(
            FindSuchThat::builder()
                .vars(cvars)
                .bound_var(bvars)
                .skolems(skolems)
                .freshes(freshes)
                .temporary(temporary)
                .tlf(tlf)
                .build()
                .into(),
        );

        // return
        match q {
            Quantifier::FindSuchThat(q) => q,
            _ => unreachable!(),
        }
    }
}

impl FindSuchThat {
    pub fn is_uninit(&self) -> bool {
        self.condition().is_none() || self.then_branch().is_none() || self.else_branch().is_none()
    }

    pub fn functions(&self) -> FindSuchThatFuns {
        let Self {
            tlf,
            skolems,
            freshes,
            ..
        } = self;
        FindSuchThatFuns {
            tlf: tlf.clone(),
            skolem: skolems.iter().cloned().collect(),
            fresh: freshes.iter().cloned().collect(),
        }
    }

    pub fn condition(&self) -> Option<&Formula> {
        self.condition.as_ref()
    }

    pub fn set_condition(&mut self, condition: Formula) {
        self.condition = Some(condition)
    }

    pub fn then_branch(&self) -> Option<&Formula> {
        self.then_branch.as_ref()
    }

    pub fn set_then_branch(&mut self, then_branch: Formula) {
        self.then_branch = Some(then_branch)
    }

    pub fn else_branch(&self) -> Option<&Formula> {
        self.else_branch.as_ref()
    }

    pub fn set_else_branch(&mut self, else_branch: Formula) {
        self.else_branch = Some(else_branch)
    }

    pub fn arguments(&self) -> Option<[&Formula; 3]> {
        Some([self.condition()?, self.then_branch()?, self.else_branch()?])
    }
}

#[derive(Debug)]
pub struct FindSuchThatFuns {
    pub tlf: Function,
    pub skolem: Rc<[Function]>,
    pub fresh: Rc<[Function]>,
}

// #[derive(Debug)]
// pub struct FindSuchThatBuilder {
//     /// The free variables captured by the quantifier
//     pub vars: Vec<Var>,
//     /// The variable bound by the quantifier
//     pub bound_var: Vec<Var>,
//     /// The "content" of the quantifier
//     pub condition: PatternAst<Lang>,
//     pub then_branch: PatternAst<Lang>,
//     pub else_branch: PatternAst<Lang>,
// }

impl Display for FindSuchThat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let FindSuchThat {
            vars,
            bound_var,
            temporary: _,
            condition,
            then_branch,
            else_branch,
            tlf,
            skolems,
            freshes,
        } = self;
        let vars = vars.iter().join(", ");
        let bound_vars = bound_var.iter().join(", ");
        let skolems = skolems.iter().join(", ");
        let freshes = freshes.iter().join(", ");

        let [condition, then_branch, else_branch] =
            [condition, then_branch, else_branch].map(|f| match f {
                Some(f) => f.to_string(),
                None => " ∅".to_string(),
            });

        write!(
            f,
            "try find [{tlf}({vars}) {bound_vars}] {freshes}; {skolems} such that {condition} \
             then {then_branch} else {else_branch}"
        )
    }
}
