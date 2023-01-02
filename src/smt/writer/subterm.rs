use itertools::Itertools;

use crate::{
    formula::{
        builtins::{
            functions::{INPUT, LT_NAME, SUBTERM},
            types::{BOOL, STEP},
        },
        env::Environement,
        formula::{sorts_to_variables, Variable},
        function::{FFlags, Function},
        sort::Sort,
    },
    smt::{
        macros::{sand, sexists, sforall, sfun, simplies, snot, sor},
        smt::{Smt, SmtFormula},
    },
};

use super::Ctx;

pub enum Subterm<'b> {
    VampireSpecial(Sort, &'b Function, Function, Function),
    Base(Sort, Function, Function),
}

pub(crate) enum OneSubterm<'a, 'b> {
    Main(&'a Subterm<'b>),
    Secondary(&'a Subterm<'b>),
}

impl<'b> Subterm<'b> {
    pub fn main(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        match self {
            Subterm::VampireSpecial(_, sbt, f, _) => sfun!(*sbt; sfun!(f), a, b),
            Subterm::Base(_, f, _) => sfun!(f; a, b),
        }
    }
    pub fn secondary(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        match self {
            Subterm::VampireSpecial(_, sbt,  _, f) => sfun!(*sbt; sfun!(f), a, b),
            Subterm::Base(_, _, f) => sfun!(f; a, b),
        }
    }

    fn as_tuple(&self) -> (&Function, &Function) {
        match self {
            Subterm::VampireSpecial(_, _, a, b) => (a, b),
            Subterm::Base(_, a, b) => (a, b),
        }
    }

    pub fn name_main(&self) -> &str {
        self.as_tuple().0.name()
    }

    pub fn name_secondary(&self) -> &str {
        self.as_tuple().1.name()
    }

    fn as_main<'a>(&'a self) -> OneSubterm<'a, 'b> {
        OneSubterm::Main(self)
    }

    fn as_secondary<'a>(&'a self) -> OneSubterm<'a, 'b> {
        OneSubterm::Secondary(self)
    }

    pub fn sort(&self) -> &Sort {
        match self {
            Subterm::VampireSpecial(s, _, _, _) => s,
            Subterm::Base(s, _, _) => s,
        }
    }

    pub(crate) fn iter<'a>(&'a self) -> impl Iterator<Item = OneSubterm<'a, 'b>> {
        [self.as_main(), self.as_secondary()].into_iter()
    }
}

impl<'a, 'b> OneSubterm<'a, 'b> {
    pub fn f(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        match self {
            OneSubterm::Main(s) => s.main(a, b),
            OneSubterm::Secondary(s) => s.secondary(a, b),
        }
    }

    pub fn name(&self) -> &str {
        match self {
            OneSubterm::Main(s) => s.name_main(),
            OneSubterm::Secondary(s) => s.name_secondary(),
        }
    }

    fn inner(&self) -> &'a Subterm<'b> {
        match self {
            OneSubterm::Main(s) => s,
            OneSubterm::Secondary(s) => s,
        }
    }

    pub fn sort(&self) -> &'a Sort {
        self.inner().sort()
    }
}

pub(crate) fn generate_subterm<'a>(
    env: &'a Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'a>,
    name: &str,
    sort: &Sort,
    functions: Vec<&Function>,
) -> Subterm<'a> {
    debug_assert!(env.verify_f());
    debug_assert!(
        functions
            .iter()
            .all(|f| env.contains_f(f)),
        "\n\tfuns: {:?}\n\tf2: {:?}",
        &functions,
        env.get_functions_iter().collect_vec()
    );

    let subt = if env.use_special_subterm() {
        generate_special_subterm(env, assertions, declarations, ctx, name, sort, functions)
    } else {
        todo!()
    };

    // spliting(assertions, declarations, ctx, subt.as_main());
    // spliting(assertions, declarations, ctx, subt.as_secondary());

    for s in subt.iter(){
        spliting(env, assertions, declarations, ctx, s);
    }

    subt
}
fn generate_special_subterm<'a>(
    env: &'a Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'a>,
    name: &str,
    sort: &Sort,
    functions: Vec<&Function>,
) -> Subterm<'a> {
    let bool = BOOL(env);


    let input = INPUT(env);
    let f_main = Function::new_with_flag(name, vec![], bool.clone(), FFlags::SUBTERM_FUN);
    let f_secondary = Function::new_with_flag(
        &format!("{}_bis", name),
        vec![],
        bool.clone(),
        FFlags::SUBTERM_FUN,
    );
    let subt = Subterm::VampireSpecial(sort.clone(), SUBTERM(env), f_main.clone(), f_secondary.clone());

    let funs_main = env.get_functions_iter()
        .filter(|&f| f.is_term_algebra() && !f.is_special_subterm() && !functions.contains(&f))
        .cloned()
        .collect_vec();
    let funs_secondary = funs_main
        .iter()
        .cloned()
        .chain(std::iter::once(input.clone()))
        .collect_vec();

    declarations.push(Smt::DeclareSubtermRelation(f_main, funs_main.clone()));
    declarations.push(Smt::DeclareSubtermRelation(
        f_secondary,
        funs_secondary.clone(),
    ));

    for s in env.get_sort_iter()
        .filter(|&s| (s != sort) && !s.is_term_algebra())
    {
        assertions.push(Smt::Assert(
            sforall!(m!1:sort, m2!2:s; {snot!(env; subt.main(m, m2))}),
        ));
        assertions.push(Smt::Assert(
            sforall!(m!1:sort, m2!2:s; {snot!(env; subt.secondary(m, m2))}),
        ));
    }
    assertions.push(Smt::Assert(sforall!(m!1:sort; {subt.main(m.clone(), m)})));
    assertions.push(Smt::Assert(
        sforall!(m!1:sort; {subt.secondary(m.clone(), m)}),
    ));

    subt
}

fn spliting(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
    subt: OneSubterm,
) {
    let input = INPUT(env);
    let lt = env.get_f(LT_NAME).unwrap();
    // biggest than any step variable
    let max_var = ctx
        .pbl
        .steps
        .values()
        .map(|s| s.parameters().len())
        .max()
        .unwrap_or(0)
        + 1;
    // make ununsed variables
    let sorts = vec![subt.sort().clone(), STEP(env).clone()];
    let vars = sorts_to_variables(max_var, sorts.iter());

    declarations.reserve(ctx.pbl.steps.len());
    assertions.reserve(ctx.pbl.steps.len() + 1);
    let mut premises = Vec::with_capacity(ctx.pbl.steps.len());

    let m = SmtFormula::from(&vars[0]);
    let tp = SmtFormula::from(&vars[1]);

    for s in ctx.pbl.steps.values() {
        let sp = Function::new_with_flag(
            &format!("sp${}${}", subt.name(), s.name()),
            sorts.clone(),
            BOOL(env).clone(),
            FFlags::SPLITING,
        );
        let sp_const = sfun!(sp, vars.iter().map_into().collect());

        declarations.push(Smt::DeclareFun(sp.clone()));
        premises.push(sp_const.clone());

        // variables 0 was `in`
        let step_vars = sorts_to_variables(1, s.parameters().iter());

        assertions.push(Smt::Assert(sforall!(
            vars.clone(),
            simplies!(env;
                sp_const.clone(),
                sexists!(
                    step_vars.clone(),
                    sand!(
                        sfun!(lt; sfun!(
                            s.function(), 
                            step_vars.iter().map_into().collect()), 
                        tp.clone()),
                        sor!(
                            subt.f(m.clone(), s.message().into()),
                            subt.f(m.clone(), s.condition().into())
                        )
                    )
                )
            )
        )))
    }

    assertions.push(Smt::Assert(sforall!(
        vars.clone(),
        simplies!(env;
            subt.f(m.clone(), sfun!(input; tp.clone())),
            SmtFormula::Or(premises)
        )
    )))
}
