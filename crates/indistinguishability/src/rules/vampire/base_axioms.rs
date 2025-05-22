use cryptovampire_smt::Smt;
use itertools::chain;

use crate::{
    const_fun_flags,
    terms::{Function, FunctionFlags, Signature, Sort, SORT_LIST},
    Problem,
};

static SHOULD_NOT_DECLARE_IN_SMT: FunctionFlags = const_fun_flags!(ALIAS | PROLOG_ONLY);

#[inline]
fn should_declare_in_smt(fun: &Function) -> bool {
    !fun.flags.intersects(SHOULD_NOT_DECLARE_IN_SMT)
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
