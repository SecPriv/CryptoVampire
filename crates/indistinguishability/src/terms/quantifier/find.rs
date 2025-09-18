use std::collections::HashSet;
use std::fmt::{Display, write};
use std::rc::Rc;

use bon::{Builder, bon, builder};
use egg::{PatternAst, Var};
use itertools::{Itertools, chain};
use logic_formula::Formula;
use utils::{ereturn_if, implvec};

use crate::rules::utils::fresh;
use crate::terms::quantifier::default_valid;
use crate::terms::{
    Function, FunctionCollection, FunctionFlags, InnerFunction, Quantifier, QuantifierIndex, QuantifierT, RecExprIter, Signature, Sort, FIND_SUCH_THAT
};
use crate::{Lang, LangVar, Problem};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Builder)]
#[builder(builder_type = FindSuchThatBuilder0)]
pub struct FindSuchThat {
    /// The free variables captured by the quantifier
    vars: Rc<[Var]>,
    /// The variable bound by the quantifier
    bound_var: Rc<[Var]>,
    #[builder(default = true)]
    temporary: bool,
    /// The "content" of the quantifier
    #[builder(default = std::iter::empty().collect())]
    condition: PatternAst<Lang>,
    #[builder(default = std::iter::empty().collect())]
    then_branch: PatternAst<Lang>,
    #[builder(default = std::iter::empty().collect())]
    else_branch: PatternAst<Lang>,
    /// the main alias (e.g., `exists$1`)
    ///
    /// stands for "top level function"
    tlf: Function,
    /// the skolem function
    skolems: Rc<[Function]>,
    /// the fresh constant replacing the index
    freshes: Rc<[Function]>,
}

impl QuantifierT for FindSuchThat {
    fn bvars(&self) -> &[Var] {
        &self.bound_var
    }

    fn cvars(&self) -> &[Var] {
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
            ereturn_if!(all_vars_set.insert(*v), false)
        }
        let all_vars_set = all_vars_set;

        let patterns_vars: HashSet<_> = [self.condition(), self.then_branch(), self.else_branch()]
            .into_iter()
            .flat_map(|x| RecExprIter::new(x).free_vars_iter())
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
        #[builder(with = FromIterator::from_iter, default = vec![])] cvars_sort: Vec<Sort>,
        #[builder(with = FromIterator::from_iter, default = vec![])] bvars_sorts: Vec<Sort>,
        #[builder(default = true)] temporary: bool,
    ) -> &mut FindSuchThat {
        assert!(!bvars_sorts.is_empty());
        // set up
        let bvars: Rc<[_]> = bvars_sorts
            .iter()
            .enumerate()
            .map(|(i, _)| egg::Var::from_u32(i as u32))
            .collect();
        let cvars: Rc<[_]> = cvars_sort
            .iter()
            .enumerate()
            .map(|(i, _)| egg::Var::from_u32((i + bvars.len()) as u32))
            .collect();

        let quant_idx = pbl.functions().quantifiers(temporary).len();

        // let n_quant = QUANTIFIER_COUNT.fetch_add(1, std::sync::atomic::Ordering::AcqRel);

        // build the Functions
        let tlf;
        let skolems: Rc<[_]>;
        let freshes: Rc<[_]>;

        {
            tlf = pbl
                .declare_function()
                .fresh_name("_findst")
                .inputs(chain!(
                    cvars_sort.iter().copied(),
                    bvars_sorts.iter().copied()
                ))
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
                        .inputs(cvars_sort.iter().copied())
                        .output(bs)
                        .quantifier_idx(quant_idx)
                        .flag(FunctionFlags::SKOLEM)
                        .set_temporary(temporary)
                        .call(),
                );
            }
            skolems = skolem_vec.into();
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
            freshes = fresh_vec.into();
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
        self.condition().is_empty()
            || self.then_branch().is_empty()
            || self.else_branch().is_empty()
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
            skolem: skolems.clone(),
            fresh: freshes.clone(),
        }
    }

    pub fn condition(&self) -> &[LangVar] {
        &self.condition
    }

    pub fn set_condition(&mut self, condition: implvec!(LangVar)) {
        self.condition = condition.into_iter().collect()
    }

    pub fn then_branch(&self) -> &[LangVar] {
        &self.then_branch
    }

    pub fn set_then_branch(&mut self, then_branch: implvec!(LangVar)) {
        self.then_branch = then_branch.into_iter().collect()
    }

    pub fn else_branch(&self) -> &[LangVar] {
        &self.else_branch
    }

    pub fn set_else_branch(&mut self, else_branch: implvec!(LangVar)) {
        self.else_branch = else_branch.into_iter().collect()
    }
    
}

#[derive(Debug)]
pub struct FindSuchThatFuns {
    pub tlf: Function,
    pub skolem: Rc<[Function]>,
    pub fresh: Rc<[Function]>,
}

#[derive(Debug)]
pub struct FindSuchThatBuilder {
    /// The free variables captured by the quantifier
    pub vars: Vec<Var>,
    /// The variable bound by the quantifier
    pub bound_var: Vec<Var>,
    /// The "content" of the quantifier
    pub condition: PatternAst<Lang>,
    pub then_branch: PatternAst<Lang>,
    pub else_branch: PatternAst<Lang>,
}

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

        write!(
            f,
            "try find [{tlf}({vars}) {bound_vars}] {freshes}; {skolems} such that {condition} \
             then {then_branch} else {else_branch}"
        )
    }
}
