use itertools::Itertools;

use crate::formula::{
    formula::{forall, meq, RichFormula},
    function::Function,
    sort::Sort,
    variable::{sorts_to_variables, Variable},
};

use self::traits::SubtermAux;

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

    pub fn f(&self, x: RichFormula<'bump>, m: RichFormula<'bump>) -> RichFormula<'bump> {
        self.function.f([x, m])
    }
}
