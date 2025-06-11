use cryptovampire_macros::smt;
use cryptovampire_smt::{Smt, SmtFormula, SortedVar, VarInner};
use itertools::{Itertools, chain, izip};

use crate::{
    Problem,
    rules::vampire::MSmtFormula,
    terms::{Function, FunctionFlags, SORT_LIST, Signature, Sort},
};

use super::MSmt;

#[inline]
fn should_declare_in_smt(fun: &Function) -> bool {
    !fun.is_should_not_declare_in_smt()
}

fn mk_header(pbl: &Problem) -> impl Iterator<Item = Smt<Sort, Function>> + use<'_> {
    let sorts = SORT_LIST.iter().copied().map(Smt::DeclareSort);
    let functions = pbl
        .function
        .iter()
        .filter(|&x| should_declare_in_smt(x))
        .cloned()
        .map(|fun| {
            let Signature { inputs, output } = &fun.signature;
            Smt::DeclareFun {
                args: inputs.to_vec(),
                out: *output,
                fun,
            }
        });

    chain! {
      sorts,
      functions
    }
}

fn mk_nonces_diff(pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
    use Smt::*;
    use SmtFormula::*;
    let nonces = pbl.function.nonces().collect_vec();

    // nonces are pairwise distincts
    let pairs = {
        let mut vars = Vec::with_capacity(nonces.iter().copied().map(Function::arity).sum());

        let app_nonces = nonces
            .iter()
            .copied()
            .map(|f| {
                let n = vars.len();
                vars.extend(f.signature.mk_sorted_vars(n as u32));
                smt!((f #(vars[n..].iter().cloned())*))
            })
            .collect_vec();

        smt!((forall #vars (distinct #app_nonces*)))
    };

    // a[veci] = a[vecj] => veci = vecj forall each nonce
    let singles = nonces.into_iter().map(|f| {
        let n = f.arity();
        let svars: Vec<SortedVar<_>> = chain![
            f.signature.mk_sorted_vars(0),
            f.signature.mk_sorted_vars(n as u32)
        ]
        .collect();
        let n1 = smt!((f #(svars[0..n].iter().cloned())*));
        let n2 = smt!((f #(svars[n..2*n].iter().cloned())*));
        let svars_eq = (0..n)
            .map(|i| smt!((= #(Var(svars[i].var.clone())) #(Var(svars[n+i].var.clone())))))
            .collect_vec();
        smt!((forall #svars (=> (= #n1 #n2) (and #svars_eq*))))
    });

    chain! {
        [Comment("nonce distinctness".into()),
        Assert(pairs)],
        singles.map(Assert)
    }
}
