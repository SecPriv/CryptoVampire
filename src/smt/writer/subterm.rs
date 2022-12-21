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

pub enum Subterm {
    VampireSpecial(Sort, Function, Function),
    Base(Sort, Function, Function),
}

pub(crate) enum OneSubterm<'a> {
    Main(&'a Subterm),
    Secondary(&'a Subterm),
}

impl Subterm {
    pub fn main(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        match self {
            Subterm::VampireSpecial(_, f, _) => sfun!(SUBTERM; sfun!(f), a, b),
            Subterm::Base(_, f, _) => sfun!(f; a, b),
        }
    }
    pub fn secondary(&self, a: SmtFormula, b: SmtFormula) -> SmtFormula {
        match self {
            Subterm::VampireSpecial(_, _, f) => sfun!(SUBTERM; sfun!(f), a, b),
            Subterm::Base(_, _, f) => sfun!(f; a, b),
        }
    }

    fn as_tuple(&self) -> (&Function, &Function) {
        match self {
            Subterm::VampireSpecial(_, a, b) => (a, b),
            Subterm::Base(_, a, b) => (a, b),
        }
    }

    pub fn name_main(&self) -> &str {
        self.as_tuple().0.name()
    }

    pub fn name_secondary(&self) -> &str {
        self.as_tuple().1.name()
    }

    fn as_main<'a>(&'a self) -> OneSubterm<'a> {
        OneSubterm::Main(self)
    }

    fn as_secondary<'a>(&'a self) -> OneSubterm<'a> {
        OneSubterm::Secondary(self)
    }

    pub fn sort(&self) -> &Sort {
        match self {
            Subterm::VampireSpecial(s, _, _) => s,
            Subterm::Base(s, _, _) => s,
        }
    }

    pub(crate) fn iter<'a>(&'a self) -> impl Iterator<Item = OneSubterm<'a>> {
        [self.as_main(), self.as_secondary()].into_iter()
    }
}

impl<'a> OneSubterm<'a> {
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

    fn inner(&self) -> &'a Subterm {
        match self {
            OneSubterm::Main(s) => s,
            OneSubterm::Secondary(s) => s,
        }
    }

    pub fn sort(&self) -> &'a Sort {
        self.inner().sort()
    }
}

pub(crate) fn generate_subterm(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
    name: &str,
    sort: &Sort,
    functions: Vec<&Function>,
) -> Subterm {
    debug_assert!(
        functions
            .iter()
            .all(|f| ctx.pbl.functions.get(f.name()) == Some(f)),
        "\n\tfuns: {:?}\n\tf2: {:?}",
        &functions,
        &ctx.pbl.functions
    );

    let subt = if env.use_special_subterm {
        generate_special_subterm(env, assertions, declarations, ctx, name, sort, functions)
    } else {
        todo!()
    };

    spliting(assertions, declarations, ctx, subt.as_main());
    spliting(assertions, declarations, ctx, subt.as_secondary());

    subt
}
fn generate_special_subterm(
    _env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
    name: &str,
    sort: &Sort,
    functions: Vec<&Function>,
) -> Subterm {
    let input = INPUT.clone();
    let f_main = Function::new_with_flag(name, vec![], BOOL.clone(), FFlags::SUBTERM_FUN);
    let f_secondary = Function::new_with_flag(
        &format!("{}_bis", name),
        vec![],
        BOOL.clone(),
        FFlags::SUBTERM_FUN,
    );
    let subt = Subterm::VampireSpecial(sort.clone(), f_main.clone(), f_secondary.clone());

    let funs_main = ctx
        .pbl
        .functions
        .iter()
        .map(|(_, f)| f)
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

    for s in ctx
        .pbl
        .sorts
        .iter()
        .filter(|&s| (s != sort) && !s.is_term_algebra())
    {
        assertions.push(Smt::Assert(
            sforall!(m!1:sort, m2!2:s; {snot!(subt.main(m, m2))}),
        ));
        assertions.push(Smt::Assert(
            sforall!(m!1:sort, m2!2:s; {snot!(subt.secondary(m, m2))}),
        ));
    }
    assertions.push(Smt::Assert(sforall!(m!1:sort; {subt.main(m.clone(), m)})));
    assertions.push(Smt::Assert(
        sforall!(m!1:sort; {subt.secondary(m.clone(), m)}),
    ));

    subt
}

fn spliting(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
    subt: OneSubterm,
) {
    let input = INPUT.clone();
    let lt = ctx.pbl.functions.get(LT_NAME).unwrap();
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
    let sorts = vec![subt.sort().clone(), STEP.clone()];
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
            BOOL.clone(),
            FFlags::SPLITING,
        );
        let sp_const = sfun!(sp, vars.iter().map_into().collect());

        declarations.push(Smt::DeclareFun(sp.clone()));
        premises.push(sp_const.clone());

        // variables 0 was `in`
        let step_vars = sorts_to_variables(1, s.parameters().iter());

        assertions.push(Smt::Assert(sforall!(
            vars.clone(),
            simplies!(
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
        simplies!(
            subt.f(m.clone(), sfun!(input; tp.clone())),
            SmtFormula::Or(premises)
        )
    )))
}
