use itertools::Itertools;

use crate::{
    formula::{builtins::types::NONCE, env::Environement, formula::Variable},
    smt::{
        macros::*,
        smt::{Smt, SmtFormula},
    },
};

use super::Ctx;

pub(crate) fn nonce_pseudo_ta(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    _declarations: &mut Vec<Smt>,
    ctx: &Ctx,
) {
    let free_funs = &ctx.free_funs;
    let nonce = NONCE(env);
    let nonces = free_funs
        .iter()
        .filter(|&f| &f.get_output_sort() == nonce)
        .map(|f| f)
        .collect_vec();

    assertions.push({
        let mut i = 0;
        let (vars, nonces): (Vec<_>, Vec<_>) = nonces
            .iter()
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

    for n in nonces {
        let vars1 = n
            .get_input_sorts()
            .iter()
            .enumerate()
            .map(|(id, s)| Variable {
                id,
                sort: s.clone(),
            })
            .collect_vec();
        let vars2 = vars1
            .iter()
            .map(|v| Variable {
                id: vars1.len() + v.id,
                sort: v.sort.clone(),
            })
            .collect_vec();

        assertions.push(Smt::Assert(sforall!(
            vars1
                .iter()
                .chain(vars2.iter())
                .map(|v| v.clone())
                .collect_vec(),
            simplies!(env;
                seq!(
                    sfun!(n, vars1.iter().map_into().collect()),
                    sfun!(n, vars2.iter().map_into().collect())
                ),
                SmtFormula::And(
                    vars1
                        .into_iter()
                        .zip(vars2.into_iter())
                        .map(|(v1, v2)| { seq!(svar!(v1), svar!(v2)) })
                        .collect_vec()
                )
            )
        )))
    }
}
