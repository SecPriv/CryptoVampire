use cryptovampire_macros::smt;
use cryptovampire_smt::{uvar, Smt, SortedVar, VarInner};
use itertools::{chain, izip, Itertools};

use crate::{
    terms::{flags::SPECIAL_SUBTERM, Function, FunctionFlags, Sort, INDEP},
    Problem,
};

use super::MSmt;

fn default_fresh(f: &&Function) -> bool {
    !f.flags.intersects(SPECIAL_SUBTERM)
        && f.signature.output ==Sort::Bitstring
}

fn mk_base_fresh(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    let sort = Smt::DeclareDatatypes { sorts: vec![Sort::SubtermStatus], cons: vec![
        vec![]
    ] };


    let funs = pbl.function.iter().filter(default_fresh);
    let status = SortedVar {
        var: VarInner::Int(0),
        sort: Sort::SubtermStatus,
    };
    let nonce = SortedVar {
        var: VarInner::Int(1),
        sort: Sort::Nonce,
    };

    let funs = funs.map(move |f| {
        let args = izip!(2.., f.signature.inputs_iter())
            .map(|(var, sort)| SortedVar {
                var: VarInner::Int(var),
                sort,
            })
            .collect_vec();

        let premise = args
            .iter()
            .filter(|s| matches!(s.sort, Sort::Bitstring | Sort::Bool))
            .map(|v| smt!((INDEP #status #nonce #v)));

        let vars = chain!([&status, &nonce], &args).cloned().collect_vec();

        smt!((forall #vars (=> (and #premise*) (INDEP #status #nonce (f #args*)))))
    })
    .map(Smt::mk_assert);

    chain!(funs)
}

#[cfg(test)]
mod test {
    use itertools::Itertools;

    use crate::{rules::vampire::fresh::mk_base_fresh, terms::BUILTINS, Problem};

    use super::default_fresh;

    #[test]
    fn print_default_default_fresh() {
        let str = mk_base_fresh(&Problem::base_empty()).join("\n");
        println!("{str}")
    }
}