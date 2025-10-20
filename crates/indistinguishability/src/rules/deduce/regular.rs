use egg::Pattern;
use golgge::PrologRule;
use itertools::izip;

use crate::problem::{PRule, RcRule};
use crate::rules::deduce::{self, GetDeduce};
use crate::terms::{Function, RecFOFormula};
use crate::{Lang, Problem, fresh, rexp};

/// Generate the base deduce rules:
///
/// ```text
/// u, v |> x0, y0 # h, h'  ...  u, v |> xn, yn # h, h'
/// ---------------------------------------------------
///     u, v |> f(x0,...,xn), f(y0,...,yn) # h, h'
/// ```
///
/// for all "regular" `f`s
pub fn mk_rules(pbl: &Problem) -> impl Iterator<Item = RcRule> + use<'_> {
    pbl.functions()
        .iter_current()
        .filter(|x| should_process_normaly(x))
        .map(mk_deduce_rule)
        .map(|x| x.into_mrc())
}

fn should_process_normaly(f: &Function) -> bool {
    !f.is_special_deduce() && f.signature.output.support_deduce()
}

/// ```text
/// u, v |> x0, y0 # h, h'  ...  u, v |> xn, yn # h, h'
/// ---------------------------------------------------
///     u, v |> f(x0,...,xn), f(y0,...,yn) # h, h'
/// ```
fn mk_deduce_rule(f: &Function) -> PrologRule<Lang> {
    assert!(should_process_normaly(f));
    let deduce = f.try_get_deduce().unwrap();
    let [u, v, h1, h2] = &::std::array::from_fn(|_| fresh!());
    let [args1, args2] = ::std::array::from_fn(|_| f.signature.mk_vars());
    let [args1, args2] = [&args1, &args2].map(|a| a.iter().map(|v| RecFOFormula::Var(v.clone())));

    let deps = izip!(args1.clone(), args2.clone(), f.signature.inputs.iter())
        .filter_map(|(a1, a2, &s)| {
            let deduce = s.try_get_deduce()?;
            Some(rexp!((deduce #u #v #a1 #a2 #h1 #h2)))
        })
        .map(|x| Pattern::from(&x))
        .collect();
    let input = Pattern::from(&rexp!((deduce #u #v (f #args1*) (f #args2*) #h1 #h2)));

    PrologRule {
        input,
        deps,
        cut: false,
        require_decrease: false,
        name: Some(format!("deduce {}", &f.name)),
    }
}

// fn mk_input(f: &Function, s: Sort, vars: [Var; 4], left: &[Var], right: &[Var]) -> Pattern<Lang> {
//     let left = f.app_var(&var_as_recexpr(left));
//     let right = f.app_var(&var_as_recexpr(right));
//     let vars = var_as_recexpr(&vars);
//     let ast: RecExpr<LangVar> = s.get_deduce().app_var(&[
//         vars[0].as_slice(),
//         &vars[1],
//         &left,
//         &right,
//         &vars[2],
//         &vars[3],
//     ]);
//     Pattern::new(ast)
// }

// /// this generate `u,v|>a, b#h1, h2` using the right sort
// ///
// /// `vars` is [u, v, a, b, h1, h2]
// fn mk_dep(vars: [Var; 6], s: Sort) -> Option<Pattern<Lang>> {
//     let vars = var_as_recexpr(&vars);
//     let ast = s.try_get_deduce()?.app_var(&vars);
//     Some(Pattern::new(ast))
// }
