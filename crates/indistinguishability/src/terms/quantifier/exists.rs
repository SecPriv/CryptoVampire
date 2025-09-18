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
    Function, FunctionCollection, FunctionFlags, InnerFunction, QUANTIFIER_COUNT, Quantifier,
    QuantifierT, Signature, Sort,
};
use crate::{Lang, LangVar, Problem};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Builder)]
#[builder(builder_type = ExistsBuilder0)]
pub struct Exists {
    /// The free variables captured by the quantifier
    vars: Rc<[Var]>,
    /// The variable bound by the quantifier
    bound_var: Rc<[Var]>,
    /// The "content" of the quantifier
    #[builder(default = std::iter::empty().collect())]
    patt: PatternAst<Lang>,
    /// the main alias (e.g., `exists$1`)
    ///
    /// stands for "top level function"
    tlf: Function,
    /// the skolem function
    skolems: Rc<[Function]>,
    /// the fresh constant replacing the index
    freshes: Rc<[Function]>,
}

impl QuantifierT for Exists {
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

    fn valid(&self, idx: usize, pbl: &crate::Problem) -> bool {
        ereturn_if!(!default_valid(self, idx, pbl), false);

        let mut all_vars_set = HashSet::with_capacity(self.bvars().len() + self.cvars().len());
        for v in chain![self.bvars(), self.cvars()] {
            ereturn_if!(all_vars_set.insert(*v), false)
        }
        let all_vars_set = all_vars_set;

        let pattern_vars: HashSet<_> = self.patt.free_vars_iter().collect();

        all_vars_set.is_superset(&pattern_vars)
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
}

#[bon]
impl Exists {
    /// The returned [Exists] has it's [Exists::vars], [Exists::bound_var] and
    /// [Exists::patt] left empty.
    #[builder]
    pub fn insert(
        pbl: &mut Problem,
        #[builder(with = FromIterator::from_iter, default = vec![])] cvars_sort: Vec<Sort>,
        #[builder(with = FromIterator::from_iter, default = vec![])] bvars_sorts: Vec<Sort>,
    ) -> &mut Exists {
        todo!("redo");
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

        let exists_idx = pbl.functions().quantifiers().len();

        let n_exists = QUANTIFIER_COUNT.fetch_add(1, std::sync::atomic::Ordering::AcqRel);

        // build the Functions
        let tlf;
        let skolems: Rc<[_]>;
        let freshes: Rc<[_]>;

        {
            // tlf
            let inner_tlf = {
                let name = format!("_exists${n_exists:}").into();
                let inputs = chain!(cvars_sort.iter().copied(), bvars_sorts.iter().copied());
                let signature = Signature::new(inputs, Sort::Bool);
                InnerFunction {
                    flags: FunctionFlags::BINDER,
                    quantifier_idx: exists_idx,
                    ..InnerFunction::new(name, signature)
                }
            };
            tlf = Function::new(inner_tlf);
            pbl.functions().add(tlf.clone());
        }

        {
            // skolem
            let mut skolem_vec = Vec::with_capacity(bvars_sorts.len());
            for (i, &bs) in bvars_sorts.iter().enumerate() {
                let inner_skolem = {
                    let name = format!("_sk${n_exists:}_{i:}").into();
                    let inputs = cvars_sort.iter().copied();
                    let signature = Signature::new(inputs, bs);
                    InnerFunction {
                        flags: FunctionFlags::SKOLEM,
                        quantifier_idx: exists_idx,
                        ..InnerFunction::new(name, signature)
                    }
                };
                let sk = Function::new(inner_skolem);
                pbl.functions().add(sk.clone());
                skolem_vec.push(sk);
            }
            skolems = skolem_vec.into();
        }

        {
            // fresh
            let mut fresh_vec = Vec::with_capacity(bvars_sorts.len());
            for (i, &bs) in bvars_sorts.iter().enumerate() {
                let inner_fresh = {
                    let name = format!("_exists_fresh${n_exists:}_{i:}").into();
                    let signature = Signature::new([], bs);
                    InnerFunction {
                        flags: FunctionFlags::QUANTIFIER_FRESH,
                        quantifier_idx: exists_idx,
                        ..InnerFunction::new(name, signature)
                    }
                };
                let frsh = Function::new(inner_fresh);
                pbl.functions().add(frsh.clone());
                fresh_vec.push(frsh);
            }
            freshes = fresh_vec.into();
        }

        let q = pbl.functions().push_quantifier(
            Exists::builder()
                .vars(cvars)
                .bound_var(bvars)
                .skolems(skolems)
                .freshes(freshes)
                .tlf(tlf)
                .build()
                .into(),
        );

        // return
        match q {
            Quantifier::Exists(q) => q,
            _ => unreachable!(),
        }
    }
}

impl Exists {
    pub fn is_uninit(&self) -> bool {
        self.patt.is_empty()
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

    pub fn patt(&self) -> &[LangVar] {
        &self.patt
    }

    pub fn set_patt(&mut self, patt: implvec!(LangVar)) {
        self.patt = patt.into_iter().collect();
    }
}

#[derive(Debug)]
pub struct ExistsFuns {
    pub tlf: Function,
    pub skolem: Rc<[Function]>,
    pub fresh: Rc<[Function]>,
}

#[derive(Debug)]
pub struct ExistsBuilder {
    /// The free variables captured by the quantifier
    pub vars: Vec<Var>,
    /// The variable bound by the quantifier
    pub bound_var: Vec<Var>,
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

        write!(
            f,
            "∃{tlf}({vars}) {bound_vars}@({freshes}; {skolems}). {patt}"
        )
    }
}
