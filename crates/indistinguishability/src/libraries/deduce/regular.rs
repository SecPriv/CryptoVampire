use egg::Pattern;
use golgge::PrologRule;
use itertools::izip;

use crate::libraries::deduce::GetDeduce;
use crate::problem::{PRule, RcRule};
use crate::terms::{Formula, Function};
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
    !f.is_special_deduce() && f.signature.output.is_base()
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
    let [args1, args2] = [&args1, &args2].map(|a| a.iter().map(|v| Formula::Var(v.clone())));

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
        payload: None,
    }
}
