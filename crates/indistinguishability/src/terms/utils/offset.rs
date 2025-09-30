use egg::{ENodeOrVar, PatternAst, Var, VarExposed};
use utils::implvec;

#[inline]
pub fn var(amount: u32, mut var: Var) -> Var {
    var_mut(amount, &mut var);
    var
}

#[inline]
pub fn var_mut(amount: egg::uvar, var: &mut Var) {
    if let VarExposed::Num(i) = var.expose() {
        *var = (i + amount).into()
    }
}

pub fn rexpr_mut<L>(amount: egg::uvar, f: &mut [ENodeOrVar<L>]) {
    for e in f {
        if let ENodeOrVar::Var(v) = e {
            var_mut(amount, v);
        }
    }
}

pub fn rexpr_owned<L>(amount: u32, f: implvec!(ENodeOrVar<L>)) -> PatternAst<L> {
    let mut f: PatternAst<L> = f.into_iter().collect();
    rexpr_mut(amount, &mut f);
    f
}
