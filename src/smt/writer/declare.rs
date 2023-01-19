use itertools::Itertools;

use crate::{
    formula::env::Environement,
    smt::smt::{Smt, SmtCons},
};

use super::Ctx;

pub(crate) fn declare(
    _env: &Environement,
    _assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx,
) {
    let free_sorts = &ctx.free_sorts;
    let ta_sorts = &ctx.ta_sorts;
    let free_funs = &ctx.free_funs;
    let ta_funs = &ctx.ta_funs;

    // free sorts
    declarations.extend(
        free_sorts
            .into_iter()
            .unique()
            .filter_map(|s| (!s.is_built_in()).then_some(Smt::DeclareSort(s.clone()))),
    );

    // ta
    let cons = ta_sorts
        .iter()
        .map(|s| {
            ta_funs
                .iter()
                .filter(|&f| &f.get_output_sort() == s)
                .map(|f| SmtCons {
                    fun: f.clone(),
                    dest: f.generate_new_destructor(),
                })
                .collect_vec()
        })
        .collect_vec();
    declarations.push(Smt::DeclareDatatypes {
        sorts: ta_sorts.iter().map(|s| s.clone()).collect(),
        cons,
    });

    // free funs
    declarations.extend(
        free_funs
            .iter()
            .filter_map(|f| (!f.is_built_in()).then_some(Smt::DeclareFun(f.clone()))),
    );
}
