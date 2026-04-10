use egg::Pattern;
use golgge::PrologRule;
use itertools::izip;
use utils::econtinue_if;

use crate::libraries::deduce::GetDeduce;
/// Generate the base deduce rules:
///
/// ```text
/// u, v |> x0, y0 # h, h'  ...  u, v |> xn, yn # h, h'
/// ---------------------------------------------------
///     u, v |> f(x0,...,xn), f(y0,...,yn) # h, h'
/// ```
///
/// for all "regular" `f`s
use crate::libraries::utils::RuleSink;
use crate::problem::{PRule, RcRule};
use crate::terms::{Formula, Function};
use crate::{Lang, Problem, fresh, rexp};

pub fn add_rules(pbl: &Problem, sink: &mut impl RuleSink) {
    for f in pbl.functions().iter_current() {
        econtinue_if!(!should_process_normaly(f));
        sink.add_rule(mk_deduce_rule(f));
    }
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
