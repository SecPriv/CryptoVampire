use std::{
    hash::Hash,
    rc::{Rc, Weak},
};

use itertools::Itertools;

use crate::{
    container::ScopeAllocator,
    formula::{
        file_descriptior::declare::{self, Declaration},
        formula::{exists, forall, meq, RichFormula},
        function::{self, Function, InnerFunction},
        sort::Sort,
        utils::{
            formula_expander::{ExpantionContent, ExpantionState, InnerExpantionState},
            formula_iterator::{FormulaIterator, IteratorFlags},
        },
        variable::{sorts_to_variables, Variable}, unifier::Unifier,
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
        container: &'bump impl ScopeAllocator<'bump, InnerFunction<'bump>>,
        name: String,
        kind: SubtermKind,
        aux: Aux,
        ignored_functions: impl IntoIterator<Item = Function<'bump>>,
        to_enum: F,
    ) -> Rc<Self>
    where
        F: FnOnce(Rc<Self>) -> function::subterm::Subsubterm<'bump>,
    {
        let ignored_functions = ignored_functions.into_iter().collect();
        let (_, self_rc) = unsafe {
            Function::new_cyclic(container, |function| {
                // let subterm = ;
                let self_rc = Rc::new_cyclic(|weak| Subterm {
                    function,
                    aux,
                    ignored_functions,
                    kind,
                    weak: Weak::clone(weak),
                });
                //  Rc::new(subterm);
                let inner = function::subterm::Subterm {
                    subterm: to_enum(Rc::clone(&self_rc)),
                    name,
                };
                (inner.into_inner_function(), self_rc)
            })
        };
        self_rc
    }

    pub fn generate_function_assertions(
        &self,
        funs: impl Iterator<Item = Function<'bump>>,
    ) -> Vec<RichFormula<'bump>> {
        funs.filter(|fun| self.ignored_functions.contains(fun))
            .map(|fun| {
                let f_sorts = fun.forced_input_sort();

                let x = Variable::new(0, self.sort());
                let mut vars = sorts_to_variables(1, f_sorts);

                let vars_f = vars.iter().map(|v| v.into_formula()).collect_vec();
                let x_f = x.into_formula();

                vars.push(x);
                forall(vars, {
                    let applied_fun = fun.f(vars_f.clone());

                    let mut ors =
                        RichFormula::ors(vars_f.into_iter().map(|f| self.f(x_f.clone(), f)));

                    {
                        let o_sort = applied_fun.get_sort();
                        if o_sort.is_err() || o_sort.unwrap() == self.sort() {
                            ors = ors | meq(x_f.clone(), applied_fun.clone())
                        }
                    }

                    self.f(x_f, applied_fun) >> ors
                })
            })
            .collect()
    }

    pub fn default_subterm_functions<'a>(
        &'a self,
        pbl: &'a Problem<'bump>,
    ) -> impl Iterator<Item = Function<'bump>> + 'a {
        pbl.functions
            .iter()
            .filter(|f| f.is_default_subterm())
            .cloned()
    }

    pub fn generate_function_assertions_from_pbl(
        &self,
        pbl: &Problem<'bump>,
    ) -> Vec<RichFormula<'bump>> {
        self.generate_function_assertions(self.default_subterm_functions(pbl))
    }

    pub fn preprocess_special_assertion<'a>(
        &'a self,
        funs: impl Iterator<Item = Function<'bump>> + 'a,
        ptcl: &'a Protocol<'bump>,
        keep_guard: bool,
    ) -> impl Iterator<Item = RichFormula<'bump>> + 'a {
        let x = Variable::new(0, self.sort());
        let x_f = x.into_formula();
        funs.map(move |fun| {
            assert!(!fun.is_default_subterm());

            let f_sorts = fun.forced_input_sort();
            let vars = sorts_to_variables(1, f_sorts);
            let vars_f = vars.iter().map(|v| v.into_formula()).collect_vec();
            let f_f = fun.f(vars_f);

            let f = self.preprocess_term(ptcl, &x_f, &f_f, keep_guard);
            forall(
                vars.into_iter().chain(std::iter::once(x)),
                self.f(x_f.clone(), f_f) >> f,
            )
        })
    }

    pub fn preprocess_special_assertion_from_pbl<'a>(
        &'a self,
        pbl: &'a Problem<'bump>,
        keep_guard: bool,
    ) -> impl Iterator<Item = RichFormula<'bump>> + 'a {
        let funs = pbl
            .functions
            .iter()
            .filter(|f| {
                f.is_term_algebra()
                    && !f.is_default_subterm()
                    && !self.ignored_functions.contains(f)
            })
            .cloned();
        self.preprocess_special_assertion(funs, &pbl.protocol, keep_guard)
    }

    pub fn preprocess_whole_ptcl(
        &self,
        ptcl: &Protocol<'bump>,
        formula: &RichFormula<'bump>,
    ) -> RichFormula<'bump> {
        let pile = repeat_n_zip((), ptcl.list_top_level_terms()).collect_vec();

        let max_var = ptcl.max_var();
        let formula = formula.translate_vars(max_var);

        let iter = FormulaIterator {
            pile: StackBox::new(pile),
            passed_along: None,
            flags: IteratorFlags::QUANTIFIER,
            f: |_, f| {
                let SubtermResult { unifier, nexts } = self.aux.eval_and_next(&formula, f);
                (
                    unifier.map(|u| {
                        u.is_unifying_to_variable()
                            .and_then(|(_, v)| {
                                (v == &formula).then(|| self.f(formula.clone(), f.clone()))
                            })
                            .unwrap_or_else(|| RichFormula::ands(u.as_equalities().unwrap()))
                    }),
                    repeat_n_zip((), nexts),
                )
            },
        };

        RichFormula::ors(iter)
    }

    /// preprocess a subterm search going through inputs and cells
    ///
    /// **!!! Please ensure the variables are well placed to avoid colisions !!!**
    ///
    /// This function *will not* take care of it (nor check)
    pub fn preprocess_term_to_formula(
        &self,
        ptcl: &Protocol<'bump>,
        x: &RichFormula<'bump>,
        m: &RichFormula<'bump>,
        keep_guard: bool,
    ) -> RichFormula<'bump> {
        let steps = &ptcl.steps;
        let pile = vec![(ExpantionState::None, m)];

        let iter = FormulaIterator {
            pile: StackBox::new(pile),
            passed_along: None,
            flags: IteratorFlags::default(),
            f: |state: ExpantionState<'bump>, f| {
                let inner_iter = ExpantionContent {
                    state: state.clone(),
                    content: f,
                }
                .expand(steps.iter().cloned(), &ptcl.graph, false)
                .into_iter()
                .map(|ec| ec.as_tuple());
                let SubtermResult { unifier, nexts } = self.aux.eval_and_next(x, f);
                (
                    unifier.map(|u| {
                        let mut guard = u
                            .is_unifying_to_variable()
                            .and_then(|(_, v)| (v == x).then(|| vec![self.f(x.clone(), f.clone())]))
                            .unwrap_or_else(|| u.as_equalities().unwrap());
                        if keep_guard {
                            match state.bound_variables() {
                                Some(vars) => {
                                    let var_iter = vars.iter().cloned();
                                    match state.condition() {
                                        Some(cond) => {
                                            guard.push(cond.clone());
                                            exists(var_iter, RichFormula::ands(guard))
                                        }
                                        None => exists(var_iter, RichFormula::ands(guard)),
                                    }
                                }
                                None => RichFormula::ands(guard),
                            }
                        } else {
                            RichFormula::ands(guard)
                        }
                    }),
                    inner_iter.chain(repeat_n_zip(state.clone(), nexts)),
                )
            },
        };
        RichFormula::ors(iter)
    }

    pub fn preprocess_term<'a>(
        &'a self,
        ptrcl: Option<&'a Protocol<'bump>>,
        x: &'a RichFormula<'bump>,
        m:&'a RichFormula<'bump>,
    ) -> impl

    pub fn f(&self, x: RichFormula<'bump>, m: RichFormula<'bump>) -> RichFormula<'bump> {
        self.function.f([x, m])
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

    pub fn reflexivity(&self) -> RichFormula<'bump> {
        mforall!(x!0:self.sort(); {
            self.f(x.clone(), x.clone())
        })
    }

    pub fn not_of_sort<'a>(
        &'a self,
        sorts: impl IntoIterator<Item = Sort<'bump>> + 'a,
    ) -> impl Iterator<Item = RichFormula<'bump>> + 'a {
        sorts
            .into_iter()
            .map(|s| mforall!(x!0:self.sort(), m!1:s; {!self.f(x, m)}))
    }

    pub fn declare(&self, pbl: &Problem<'bump>) -> Declaration<'bump> {
        match self.kind {
            SubtermKind::Regular => Declaration::FreeFunction(self.function),
            SubtermKind::Vampire => Declaration::Subterm(declare::Subterm {
                name: self.function.name().to_owned(),
                functions: self.default_subterm_functions(pbl).collect(),
            }),
        }
    }
}

pub type GuardAndBound<'a> = InnerExpantionState<'a>;
pub struct SubtermSearchElement<'a, 'bump> {
    pub inner_state: Rc<GuardAndBound<'bump>>,
    pub unifier: Unifier<'a, 'bump>
}

pub trait AsSubterm<'bump> /* : Ord */ /* + std::fmt::Debug */ {
    fn generate_function_assertions(&self, funs: &[Function<'bump>]) -> Vec<RichFormula<'bump>>;
    fn f(&self, x: RichFormula<'bump>, m: RichFormula<'bump>) -> RichFormula<'bump>;
    fn function(&self) -> Function<'bump>;
    fn ignored_functions(&self) -> &[Function<'bump>];
    fn sort(&self) -> Sort<'bump>;
}

impl<'bump, Aux> AsSubterm<'bump> for Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    fn generate_function_assertions(&self, funs: &[Function<'bump>]) -> Vec<RichFormula<'bump>> {
        Subterm::generate_function_assertions(self, funs.iter().cloned())
    }

    fn f(&self, x: RichFormula<'bump>, m: RichFormula<'bump>) -> RichFormula<'bump> {
        Subterm::f(self, x, m)
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
