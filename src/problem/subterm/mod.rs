use std::{
    hash::Hash,
    rc::Rc,
    sync::{Arc, Weak},
};

use itertools::Itertools;

use crate::{
    container::allocator::ContainerTools,
    formula::{
        file_descriptior::declare::{self, Declaration},
        formula::{self, exists, forall, meq, ARichFormula},
        function::{self, Function, InnerFunction},
        manipulation::Unifier,
        sort::Sort,
        utils::{
            formula_expander::{
                DeeperKinds, ExpantionContent, ExpantionState, InnerExpantionState,
            },
            formula_iterator::{FormulaIterator, IteratorFlags},
        },
        variable::{sorts_to_variables, Variable},
    },
    mforall, partial_order,
    utils::utils::{repeat_n_zip, StackBox},
};

use self::{
    kind::SubtermKind,
    traits::{SubtermAux, SubtermResult},
};

use super::{problem::Problem, protocol::Protocol};

pub mod kind;
pub mod traits;

#[derive(Debug, Clone)]
pub struct Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    function: Function<'bump>,
    aux: Aux,
    ignored_functions: Vec<Function<'bump>>,
    pub kind: SubtermKind,
    weak: Weak<Self>, // sort: Sort<'bump>,
    deeper_kind: DeeperKinds,
}

impl<'bump, Aux> Eq for Subterm<'bump, Aux> where Aux: SubtermAux<'bump> + Eq {}
impl<'bump, Aux> Ord for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump> + Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Self::partial_cmp(&self, &other).unwrap()
    }
}
impl<'bump, Aux> PartialOrd for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump> + PartialOrd,
{
    partial_order!(function, aux, kind, ignored_functions);
}
impl<'bump, Aux> PartialEq for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump> + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.function == other.function
            && self.kind == other.kind
            && self.aux == other.aux
            && self.ignored_functions == other.ignored_functions
    }
}
impl<'bump, Aux> Hash for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump> + Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.function.hash(state);
        self.aux.hash(state);
        self.ignored_functions.hash(state);
        self.kind.hash(state);
    }
}

impl<'bump, Aux> Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    pub fn new<F>(
        container: &'bump impl ContainerTools<'bump, InnerFunction<'bump>, R<'bump> = Function<'bump>>,
        name: String,
        kind: SubtermKind,
        aux: Aux,
        ignored_functions: impl IntoIterator<Item = Function<'bump>>,
        deeper_kind: DeeperKinds,
        to_enum: F,
    ) -> Arc<Self>
    where
        F: FnOnce(Arc<Self>) -> function::inner::subterm::Subsubterm<'bump>,
    {
        let ignored_functions = ignored_functions.into_iter().collect();
        let (_, self_rc) = unsafe {
            Function::new_cyclic(container, |function| {
                // let subterm = ;
                let self_rc = Arc::new_cyclic(|weak| Subterm {
                    function: *function,
                    aux,
                    ignored_functions,
                    kind,
                    weak: Weak::clone(weak),
                    deeper_kind,
                });
                //  Rc::new(subterm);
                let inner = function::inner::subterm::Subterm {
                    subterm: to_enum(Arc::clone(&self_rc)),
                    name,
                };
                (inner.into_inner_function(), self_rc)
            })
        };
        self_rc
    }

    /// Generate default function assertions from a list of function
    ///
    /// This should not be used with "special functions" (it will crash anyway)
    fn generate_functions_assertions(
        &self,
        funs: impl Iterator<Item = Function<'bump>>,
    ) -> Vec<ARichFormula<'bump>> {
        funs.map(|fun| {
            assert!(fun.is_default_subterm());

            let f_sorts = fun.fast_insort().expect("todo");

            let x = Variable::new(0, self.sort());
            let mut vars: Vec<_> = sorts_to_variables(1, f_sorts.iter());

            let vars_f = vars.iter().map(|v| v.into_aformula()).collect_vec();
            let x_f = x.into_aformula();

            vars.push(x);
            forall(vars, {
                let applied_fun = fun.f_a(vars_f.clone());

                let mut ors = formula::ors(vars_f.into_iter().map(|f| self.f_a(x_f.clone(), f)));

                {
                    let o_sort = applied_fun.get_sort();
                    if o_sort.is_err() || o_sort.unwrap() == self.sort() {
                        ors = ors | meq(x_f.clone(), applied_fun.clone())
                    }
                }

                self.f_a(x_f, applied_fun) >> ors
            })
        })
        .collect()
    }

    /// List of functions declared to use default subterm
    pub fn list_default_subterm_functions<'a>(
        &'a self,
        pbl: &'a Problem<'bump>,
    ) -> impl Iterator<Item = Function<'bump>> + 'a {
        pbl.functions
            .iter()
            .filter(|f| f.is_default_subterm())
            .filter(|fun| !self.ignored_functions.contains(fun))
            .cloned()
    }

    pub fn generate_function_assertions_from_pbl(
        &self,
        pbl: &Problem<'bump>,
    ) -> Vec<ARichFormula<'bump>> {
        self.generate_functions_assertions(self.list_default_subterm_functions(pbl))
    }

    pub fn generate_special_functions_assertions<'a>(
        &'a self,
        funs: impl Iterator<Item = Function<'bump>> + 'a,
        ptcl: &'a Protocol<'bump>,
        keep_guard: bool,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let max_var = ptcl.max_var() + 1;
        let x = Variable::new(max_var, self.sort());
        let max_var = max_var + 1;
        let x_f = x.into_aformula();
        funs.map(move |fun| {
            assert!(!fun.is_default_subterm());

            let f_sorts = fun
                .fast_insort()
                .expect(&format!("failed here: {}", line!()));
            let vars: Vec<_> = sorts_to_variables(max_var, f_sorts.iter());
            let vars_f = vars.iter().map(|v| v.into_aformula()).collect_vec();
            let f_f = fun.f_a(vars_f);

            // no variable collision
            let f = self.preprocess_term_to_formula(ptcl, &x_f, f_f.clone(), keep_guard);
            forall(
                vars.into_iter().chain(std::iter::once(x)),
                self.f_a(x_f.clone(), f_f) >> f,
            )
        })
    }

    pub fn preprocess_special_assertion_from_pbl<'a>(
        &'a self,
        pbl: &'a Problem<'bump>,
        keep_guard: bool,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let funs = pbl
            .functions
            .iter()
            .filter(|f| {
                f.is_term_algebra()
                    && (!f.is_default_subterm() || self.ignored_functions.contains(f))
            })
            .cloned();
        self.generate_special_functions_assertions(funs, &pbl.protocol, keep_guard)
    }

    /// whach out for variable clash
    pub fn preprocess_whole_ptcl<'a>(
        &'a self,
        ptcl: &'a Protocol<'bump>,
        formula: &'a ARichFormula<'bump>,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        self.preprocess_terms(
            ptcl,
            formula,
            ptcl.list_top_level_terms_short_lifetime().cloned(),
            false,
            DeeperKinds::QUANTIFIER,
        )
    }

    /// preprocess a subterm search going through inputs and cells. Returns a formula
    ///
    /// **!!! Please ensure the variables are well placed to avoid colisions !!!**
    ///
    /// This function *will not* take care of it (nor check)
    pub fn preprocess_term_to_formula<'a>(
        &'a self,
        ptcl: &'a Protocol<'bump>,
        x: &ARichFormula<'bump>,
        m: ARichFormula<'bump>,
        keep_guard: bool,
    ) -> ARichFormula<'bump> {
        formula::ors(self.preprocess_term(ptcl, x, m, keep_guard, self.deeper_kind))
    }

    /// preprocess a subterm search going through inputs and cells. Returns a list to ored.
    ///
    /// **!!! Please ensure the variables are well placed to avoid colisions !!!**
    ///
    /// This function *will not* take care of it (nor check)
    pub fn preprocess_term<'a>(
        &'a self,
        ptcl: &'a Protocol<'bump>,
        x: &'a ARichFormula<'bump>,
        m: ARichFormula<'bump>,
        keep_guard: bool,
        deeper_kind: DeeperKinds,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        self.preprocess_terms(ptcl, &x, [m], keep_guard, deeper_kind)
    }

    /// preprocess a subterm search going through inputs and cells. Returns a list to ored.
    ///
    /// **!!! Please ensure the variables are well placed to avoid colisions !!!**
    ///
    /// This function *will not* take care of it (nor check)
    pub fn preprocess_terms<'a, 'b>(
        &'a self,
        ptcl: &'a Protocol<'bump>,
        x: &'a ARichFormula<'bump>,
        m: impl IntoIterator<Item = ARichFormula<'bump>>,
        keep_guard: bool,
        deeper_kind: DeeperKinds,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let steps = ptcl.steps();

        // let pile = vec![(ExpantionState::None, m)];
        let pile = repeat_n_zip(ExpantionState::None, m).collect_vec();

        FormulaIterator {
            pile: StackBox::new(pile),
            passed_along: None,
            flags: IteratorFlags::default(),
            f: move |state: ExpantionState<'bump>, f| {
                let inner_iter = ExpantionContent {
                    state: state.clone(),
                    content: f.clone(),
                }
                .expand(steps.iter().cloned(), ptcl.graph(), false, deeper_kind)
                .into_iter()
                .map(|ec| ec.as_tuple());
                let SubtermResult { unifier, nexts } = self.aux.eval_and_next(x, &f);
                (
                    unifier.map(|u| {
                        let mut guard = u
                            .is_unifying_to_variable()
                            .and_then(|ovs| {
                                (ovs.f() == x).then(|| vec![self.f_a(x.clone(), f.clone())])
                            })
                            .unwrap_or_else(|| u.as_equalities().unwrap());
                        if keep_guard {
                            guard.extend(state.condition().into_iter().cloned())
                        }
                        exists(
                            state
                                .bound_variables()
                                .into_iter()
                                .flat_map(|vars| vars.iter().cloned()),
                            formula::ands(guard),
                        )
                    }),
                    inner_iter.chain(repeat_n_zip(state.clone(), nexts)),
                )
            },
        }
    }

    pub fn f_a<I>(&self, x: I, m: I) -> ARichFormula<'bump>
    where
        I: Into<ARichFormula<'bump>>,
    {
        self.function.f_a([x, m])
    }

    pub fn function(&self) -> Function<'bump> {
        self.function
    }

    pub fn ignored_functions(&self) -> &[Function<'bump>] {
        self.ignored_functions.as_ref()
    }

    pub fn sort(&self) -> Sort<'bump> {
        self.aux.sort()
    }

    pub fn reflexivity(&self) -> ARichFormula<'bump> {
        mforall!(x!0:self.sort(); {
            self.f_a(x, x)
        })
    }

    pub fn not_of_sort<'a>(
        &'a self,
        sorts: impl IntoIterator<Item = Sort<'bump>> + 'a,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        sorts
            .into_iter()
            .map(|s| mforall!(x!0:self.sort(), m!1:s; {!self.f_a(x, m)}))
    }

    pub fn declare(&self, pbl: &Problem<'bump>) -> Declaration<'bump> {
        match self.kind {
            SubtermKind::Regular => Declaration::FreeFunction(self.function),
            SubtermKind::Vampire => Declaration::Subterm(declare::Subterm {
                function: self.function,
                comutative_functions: self.list_default_subterm_functions(pbl).collect(),
            }),
        }
    }
}

pub type GuardAndBound<'bump> = InnerExpantionState<'bump>;
pub struct SubtermSearchElement<'bump> {
    pub inner_state: Rc<GuardAndBound<'bump>>,
    pub unifier: Unifier<'bump>,
}

pub trait AsSubterm<'bump> {
    fn generate_function_assertions(&self, funs: &[Function<'bump>]) -> Vec<ARichFormula<'bump>>;
    fn f(&self, x: ARichFormula<'bump>, m: ARichFormula<'bump>) -> ARichFormula<'bump>;
    fn function(&self) -> Function<'bump>;
    fn ignored_functions(&self) -> &[Function<'bump>];
    fn sort(&self) -> Sort<'bump>;
}

impl<'bump, Aux> AsSubterm<'bump> for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    fn generate_function_assertions(&self, funs: &[Function<'bump>]) -> Vec<ARichFormula<'bump>> {
        Subterm::generate_functions_assertions(self, funs.iter().cloned())
    }

    fn f(&self, x: ARichFormula<'bump>, m: ARichFormula<'bump>) -> ARichFormula<'bump> {
        Subterm::f_a(self, x, m)
    }
    fn function(&self) -> Function<'bump> {
        Self::function(&self)
    }
    fn ignored_functions(&self) -> &[Function<'bump>] {
        Self::ignored_functions(&self)
    }
    fn sort(&self) -> Sort<'bump> {
        Self::sort(&self)
    }
}
