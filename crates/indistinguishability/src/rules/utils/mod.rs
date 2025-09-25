pub mod fresh;

mod search;
use egg::Var;
pub use search::{SyntaxSearcher, default_is_special};

use crate::LangVar;
use crate::terms::Function;

mod subst;
pub use subst::mk_subst_rw;

pub fn generate_rule_vars_arr<const N: usize>(
    fun: &Function,
) -> (Vec<[LangVar; 1]>, [[LangVar; 1]; N]) {
    use egg::*;
    let (vars, others) = generate_rule_vars0(fun);
    let vars: Vec<[LangVar; 1]> = vars.map(ENodeOrVar::Var).map(|x| [x]).collect();
    let others = others.map(ENodeOrVar::Var).map(|x| [x]);
    (vars, others)
}

pub fn generate_rule_vars<const N: usize>(fun: &Function) -> (Vec<LangVar>, [LangVar; N]) {
    use egg::*;
    let (vars1, others1) = generate_rule_vars0(fun);

    let vars: Vec<LangVar> = vars1.map(ENodeOrVar::Var).collect();
    let others = others1.map(ENodeOrVar::Var);
    (vars, others)
}

pub fn generate_rule_vars0<const N: usize>(
    fun: &Function,
) -> (impl Iterator<Item = Var> + Clone + use<'_, N>, [Var; N]) {
    use egg::*;
    let n = fun.signature.inputs.len() as u32;
    let vars1 = fun
        .signature
        .inputs
        .iter()
        .enumerate()
        .map(|(i, _)| Var::from_usize(i as u32));
    let others1 = ::std::array::from_fn(|i| i as u32)
        .map(|x| x + n)
        .map(Var::from_usize);
    (vars1, others1)
}
