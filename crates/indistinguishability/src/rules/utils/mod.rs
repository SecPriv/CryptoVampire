pub mod fresh;

mod search;
pub use search::{SyntaxSearcher, default_is_special};

use crate::{LangVar, terms::Function};

mod subst;
pub use subst::mk_subst_rw;

pub fn generate_rule_vars_arr<const N: usize>(
    fun: &Function,
) -> (Vec<[LangVar; 1]>, [[LangVar; 1]; N]) {
    use egg::*;
    let vars: Vec<[LangVar; 1]> = fun
        .signature
        .inputs
        .iter()
        .enumerate()
        .map(|(i, _)| Var::from_u32(i as u32))
        .map(ENodeOrVar::Var)
        .map(|x| [x])
        .collect();
    let others = ::std::array::from_fn(|i| i as u32)
        .map(|x| x + vars.len() as u32)
        .map(Var::from_u32)
        .map(ENodeOrVar::Var)
        .map(|x| [x]);
    (vars, others)
}

pub fn generate_rule_vars<const N: usize>(fun: &Function) -> (Vec<LangVar>, [LangVar; N]) {
    use egg::*;
    let vars: Vec<LangVar> = fun
        .signature
        .inputs
        .iter()
        .enumerate()
        .map(|(i, _)| Var::from_u32(i as u32))
        .map(ENodeOrVar::Var)
        .collect();
    let others = ::std::array::from_fn(|i| i as u32)
        .map(|x| x + vars.len() as u32)
        .map(Var::from_u32)
        .map(ENodeOrVar::Var);
    (vars, others)
}
