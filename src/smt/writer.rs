use itertools::{Either, Itertools};

use crate::{
    formula::{
        builtins::{
            functions::{HAPPENS, HAPPENS_NAME, LT_NAME},
            steps::INIT,
            types::{BOOL, NONCE, STEP},
        },
        env::Environement,
        formula::{RichFormula, Variable},
        function::Function,
    },
    problem::problem::Problem,
};

use super::{
    macros::*,
    smt::{Smt, SmtCons, SmtFormula},
};

pub fn problem_to_smt(env: &Environement, pbl: Problem) -> Vec<Smt> {
    let Problem {
        steps,
        functions,
        sorts,
        assertions,
        query,
        order,
        lemmas,
        crypto_assumptions,
        quantifiers,
    } = &pbl;

    let mut smt = Vec::new();

    let (ta_funs, free_funs): (Vec<_>, Vec<_>) = functions.into_iter().partition_map(|(_, f)| {
        if f.is_term_algebra() {
            Either::Left(f)
        } else {
            Either::Right(f)
        }
    });
    let (ta_sorts, free_sorts): (Vec<_>, Vec<_>) = sorts.into_iter().partition_map(|s| {
        if s.is_term_algebra() {
            Either::Left(s)
        } else {
            Either::Right(s)
        }
    });

    // free sorts
    smt.extend(
        free_sorts
            .into_iter()
            .filter_map(|s| s.is_built_in().then_some(Smt::DeclareSort(s.clone()))),
    );

    // ta
    let cons = ta_sorts
        .iter()
        .map(|&s| {
            ta_funs
                .iter()
                .filter(|&&f| f.get_output_sort() == s)
                .map(|&f| SmtCons {
                    fun: f.clone(),
                    dest: f.generate_new_destructor(),
                })
                .collect_vec()
        })
        .collect_vec();
    smt.push(Smt::DeclareDatatypes {
        sorts: ta_sorts.into_iter().cloned().collect(),
        cons,
    });

    // free funs
    smt.extend(
        free_funs
            .iter()
            .filter_map(|&f| f.is_built_in().then_some(Smt::DeclareFun(f.clone()))),
    );

    // nonce pseudo ta
    smt.push({
        let nonce = NONCE.clone();
        let mut i = 0;
        let (vars, nonces): (Vec<_>, Vec<_>) = free_funs
            .iter()
            .filter(|&&f| f.get_output_sort() == &nonce)
            .map(|&f| {
                let vars = f
                    .get_input_sorts()
                    .iter()
                    .map(|s| {
                        i += 1;
                        Variable {
                            id: i,
                            sort: s.clone(),
                        }
                    })
                    .collect_vec();
                (
                    vars.clone(),
                    SmtFormula::Fun(
                        f.clone(),
                        vars.into_iter().map(|v| SmtFormula::Var(v)).collect_vec(),
                    ),
                )
            })
            .unzip();

        let vars = vars.into_iter().flat_map(|v| v.into_iter()).collect_vec();

        Smt::Assert(sforall!(vars, SmtFormula::Neq(nonces)))
    });

    // ordering
    {
        let init = sfun!(functions.get(INIT.name()).unwrap().clone());
        let lt = functions.get(LT_NAME).unwrap().clone();
        let happens = functions.get(HAPPENS_NAME).unwrap().clone();

        smt.push(Smt::Assert(sforall!(s!0:STEP; {
            sor!(
                sfun!(lt; init, s),
                seq!(init, s)
            )
        })));
        smt.push(Smt::Assert(sforall!(s1!1:STEP, s2!2:STEP, s3!3:STEP ;{
                simplies!(
                    sand!(
                        sfun!(lt; s1, s2),
                        sfun!(lt; s2, s3)
                    ),
                    sfun!(lt; s1, s3)
                )
        })));
        smt.push(Smt::Assert(sforall!(s1!1:STEP, s2!2:STEP; {
            simplies!(
                sand!(
                    sfun!(happens; s2),
                    sfun!(lt; s1, s2)
                ),
                sfun!(happens; s1)
            )
        })));
    }

    smt
}
