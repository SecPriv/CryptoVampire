use std::collections::HashSet;
use std::fmt::Display;

use bon::{Builder, bon};
use egg::PatternAst;
use itertools::{Itertools, chain};
use logic_formula::AsFormula;
use utils::ereturn_if;

use crate::terms::quantifier::default_valid;
use crate::terms::{Formula, Function, QuantifierIndex, QuantifierT, Sort, Variable};
use crate::{Lang, Problem};

/// For now [Exists] are never temporary
static EXISTS_TEMPORARY: bool = false;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Builder)]
#[builder(builder_type = ExistsBuilder0)]
pub struct Exists {
    /// The free variables captured by the quantifier
    vars: Vec<Variable>,
    /// The variable bound by the quantifier
    bound_var: Vec<Variable>,
    /// The "content" of the quantifier
    patt: Option<Formula>,
    /// the main alias (e.g., `exists$1`)
    ///
    /// stands for "top level function"
    tlf: Function,
    /// the skolem function
    skolems: Vec<Function>,
    /// the fresh constant replacing the index
    freshes: Vec<Function>,
}

impl QuantifierT for Exists {
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

        if let Some(patt) = &self.patt {
            let mut all_vars_set = HashSet::with_capacity(self.bvars().len() + self.cvars().len());
            for v in chain![self.bvars(), self.cvars()] {
                ereturn_if!(all_vars_set.insert(v), false)
            }
            let all_vars_set = all_vars_set;

            let pattern_vars: HashSet<_> = patt.free_vars_iter().collect();

            ereturn_if!(!all_vars_set.is_superset(&pattern_vars), false);
        }

        true
    }

    fn try_from_ref(q: &super::Quantifier) -> Option<&Self> {
        match q {
            super::Quantifier::Exists(exists) => Some(exists),
            _ => None,
        }
    }

    fn try_from_mut(q: &mut super::Quantifier) -> Option<&mut Self> {
        match q {
            super::Quantifier::Exists(exists) => Some(exists),
            _ => None,
        }
    }

    fn temporary(&self) -> bool {
        // delete static variable if changed
        EXISTS_TEMPORARY
    }
}

#[bon]
impl Exists {
    /// The returned [Exists] has it's [Exists::vars], [Exists::bound_var] and
    /// [Exists::patt] left empty.
    #[builder]
    #[deprecated]
    pub fn insert(
        _pbl: &mut Problem,
        #[builder(with = FromIterator::from_iter, default = vec![])] _cvars_sorts: Vec<Sort>,
        #[builder(with = FromIterator::from_iter, default = vec![])] _bvars_sorts: Vec<Sort>,
    ) -> &mut Exists {
        todo!("redo");
        // assert!(!bvars_sorts.is_empty());
        // // set up
        // let bvars: Rc<[_]> = bvars_sorts
        //     .iter()
        //     .enumerate()
        //     .map(|(i, _)| egg::Var::from_usize(i as u32))
        //     .collect();
        // let cvars: Rc<[_]> = cvars_sort
        //     .iter()
        //     .enumerate()
        //     .map(|(i, _)| egg::Var::from_usize((i + bvars.len()) as u32))
        //     .collect();

        // let exists_idx = pbl.functions().quantifiers(EXISTS_TEMPORARY).len();

        // // let n_exists = QUANTIFIER_COUNT.fetch_add(1, std::sync::atomic::Ordering::AcqRel);

        // // build the Functions
        // let tlf;
        // let skolems: Rc<[_]>;
        // let freshes: Rc<[_]>;
        // {
        //     tlf = pbl
        //         .declare_function()
        //         .fresh_name("_exists")
        //         .inputs(chain!(
        //             cvars_sort.iter().copied(),
        //             bvars_sorts.iter().copied()
        //         ))
        //         .output(Sort::Bitstring)
        //         .quantifier_idx(exists_idx)
        //         .flag(FunctionFlags::BINDER)
        //         .temporary()
        //         .call()
        // }

        // {
        //     // skolem
        //     let mut skolem_vec = Vec::with_capacity(bvars_sorts.len());
        //     let name = format!("_sk${}", tlf.name);
        //     for &bs in &bvars_sorts {
        //         skolem_vec.push(
        //             pbl.declare_function()
        //                 .fresh_name(&name)
        //                 .inputs(cvars_sort.iter().copied())
        //                 .output(bs)
        //                 .quantifier_idx(exists_idx)
        //                 .flag(FunctionFlags::SKOLEM)
        //                 .temporary()
        //                 .call(),
        //         );
        //     }
        //     skolems = skolem_vec.into();
        // }

        // {
        //     // fresh
        //     let mut fresh_vec = Vec::with_capacity(bvars_sorts.len());
        //     let name = format!("_fresh${}", tlf.name);
        //     for  &bs in &bvars_sorts {
        //         fresh_vec.push(
        //             pbl.declare_function()
        //                 .fresh_name(&name)
        //                 .output(bs)
        //                 .quantifier_idx(exists_idx)
        //                 .flag(FunctionFlags::QUANTIFIER_FRESH)
        //                 .temporary()
        //                 .call(),
        //         );
        //     }
        //     freshes = fresh_vec.into();
        // }

        // let q = pbl.functions_mut().push_quantifier(
        //     Exists::builder()
        //         .vars(cvars)
        //         .bound_var(bvars)
        //         .skolems(skolems)
        //         .freshes(freshes)
        //         .tlf(tlf)
        //         .build()
        //         .into(),
        // );

        // // return
        // match q {
        //     Quantifier::Exists(q) => q,
        //     _ => unreachable!(),
        // }
    }
}

impl Exists {
    #[must_use]
    pub fn is_uninit(&self) -> bool {
        self.patt.is_none()
    }

    pub fn functions(&self) -> ExistsFuns {
        let Self {
            tlf,
            skolems,
            freshes,
            ..
        } = self;
        ExistsFuns {
            tlf: tlf.clone(),
            skolem: skolems.clone(),
            fresh: freshes.clone(),
        }
    }

    pub fn patt(&self) -> Option<&Formula> {
        self.patt.as_ref()
    }

    pub fn set_patt(&mut self, patt: Formula) {
        self.patt = Some(patt);
    }
}

#[derive(Debug)]
pub struct ExistsFuns {
    pub tlf: Function,
    pub skolem: Vec<Function>,
    pub fresh: Vec<Function>,
}

#[derive(Debug)]
pub struct ExistsBuilder {
    /// The free variables captured by the quantifier
    pub vars: Vec<Variable>,
    /// The variable bound by the quantifier
    pub bound_var: Vec<Variable>,
    /// The "content" of the quantifier
    pub patt: PatternAst<Lang>,
}

impl Display for Exists {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Exists {
            vars,
            bound_var,
            patt,
            tlf,
            skolems,
            freshes,
        } = self;
        let vars = vars.iter().join(", ");
        let bound_vars = bound_var.iter().join(", ");
        let skolems = skolems.iter().join(", ");
        let freshes = freshes.iter().join(", ");

        write!(f, "∃{tlf}({vars}) {bound_vars}@({freshes}; {skolems}).")?;
        match patt {
            Some(patt) => write!(f, " {patt}"),
            None => write!(f, " ∅"),
        }
    }
}
