use itertools::Itertools;

use crate::{
    formula::{
        formula::{exists, forall, meq, RichFormula},
        function::Function,
        sort::Sort,
        utils::{
            formula_expander::{ExpantionContent, ExpantionState},
            formula_iterator::{FormulaIterator, IteratorFlags},
        },
        variable::{sorts_to_variables, Variable},
    },
    utils::utils::{repeat_n_zip, StackBox},
};

use self::traits::{SubtermAux, SubtermResult};

use super::{problem::Problem, protocol::Protocol};

pub mod traits;

pub struct Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    function: Function<'bump>,
    aux: Aux,
    ignored_functions: Vec<Function<'bump>>,
    sort: Sort<'bump>,
}

impl<'bump, Aux> Subterm<'bump, Aux>
where
    Aux: SubtermAux<'bump>,
{
    pub fn generate_function_assertions(
        &self,
        funs: impl Iterator<Item = Function<'bump>>,
    ) -> Vec<RichFormula<'bump>> {
        funs.filter(|fun| self.ignored_functions.contains(fun))
            .map(|fun| {
                let f_sorts = fun.forced_input_sort();

                let x = Variable::new(0, self.sort);
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
                        if o_sort.is_err() || o_sort.unwrap() == self.sort {
                            ors = ors | meq(x_f.clone(), applied_fun.clone())
                        }
                    }

                    self.f(x_f, applied_fun) >> ors
                })
            })
            .collect()
    }

    pub fn generate_function_assertions_from_pbl(
        &self,
        pbl: Problem<'bump>,
    ) -> Vec<RichFormula<'bump>> {
        self.generate_function_assertions(
            pbl.functions
                .iter()
                .filter(|f| f.is_term_algebra())
                .cloned(),
        )
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
                    unifier.map(|u| RichFormula::ands(u.as_equalities().unwrap())),
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
    pub fn preprocess_term(
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
                        let mut guard = u.as_equalities().unwrap();
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
        self.sort
    }
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
