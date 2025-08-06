use egg::{Pattern, RecExpr, Var};
use golgge::PrologRule;
use itertools::{Itertools, izip};
use logic_formula::egg::SimpleDiscriminant;

use crate::rules::deduce::GetDeduce;
use crate::rules::var_as_recexpr;
use crate::terms::{Function, Sort};
use crate::{Lang, LangVar, Problem};

/// Generate the base deduce rule:
///
/// ```text
/// u, v |> x0, y0 # h, h'  ...  u, v |> xn, yn # h, h'
/// ---------------------------------------------------
///     u, v |> f(x0,...,xn), f(y0,...,yn) # h, h'
/// ```
///
/// for all "regular" `f`s
pub fn mk_rules(pbl: &Problem) -> impl Iterator<Item = PrologRule<Lang>> + use<'_> {
    pbl.function
        .iter()
        .filter(|x| should_process_normaly(x))
        .map(mk_deduce_rule)
}

fn should_process_normaly(f: &Function) -> bool {
    !f.is_special_deduce() && f.signature.output.support_deduce()
}

fn mk_deduce_rule(f: &Function) -> PrologRule<Lang> {
    assert!(should_process_normaly(f));
    assert!(f.signature.output.support_deduce());
    let n: u32 = f.arity().try_into().unwrap();
    let s = f.signature.output;

    let vars @ [u, v, h1, h2] = [0, 1, 2, 3].map(Var::from_u32);
    let left_vars = (4..(4 + n)).map(Var::from_u32).collect_vec();
    let right_vars = ((4 + n)..(4 + 2 * n)).map(Var::from_u32).collect_vec();

    let input = mk_input(f, s, vars, &left_vars, &right_vars);
    let deps = izip!(f.signature.inputs_iter(), left_vars, right_vars)
        .filter_map(|(s, a, b)| mk_dep([u, v, a, b, h1, h2], s))
        .collect();

    PrologRule {
        input,
        deps,
        cut: false,
        require_decrease: false,
        name: Some(format!("deduce {}", &f.name)),
    }
}

fn mk_input(
    f: &Function,
    s: Sort,
    vars: [Var; 4],
    left: &[Var],
    right: &[Var],
) -> Pattern<logic_formula::egg::SimplLang<Function>> {
    let left = f.app_var(&var_as_recexpr(left));
    let right = f.app_var(&var_as_recexpr(right));
    let vars = var_as_recexpr(&vars);
    let ast: RecExpr<LangVar> = s.get_deduce().app_var(&[
        vars[0].as_slice(),
        &vars[1],
        &left,
        &right,
        &vars[2],
        &vars[3],
    ]);
    Pattern::new(ast)
}

/// this generate `u,v|>a, b#h1, h2` using the right sort
///
/// `vars` is [u, v, a, b, h1, h2]
fn mk_dep(vars: [Var; 6], s: Sort) -> Option<Pattern<Lang>> {
    let vars = var_as_recexpr(&vars);
    let ast = s.try_get_deduce()?.app_var(&vars);
    Some(Pattern::new(ast))
}
