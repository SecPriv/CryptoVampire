use std::ops::Deref;

use egg::{ENodeOrVar, Pattern, PatternAst, RecExpr, SymbolLang, Var};
use golgge::PrologRule;
use itertools::{chain, izip, Itertools};
use logic_formula::egg::SimpleDiscriminant;
use utils::implvec;

use crate::{
    const_fun_flags, terms::{Exists, Function, FunctionFlags, Sort, BIT_DEDUCE, BOOL_DEDUCE}, Lang, LangVar, Problem
};

use super::{
    parse::{clean_input, convert_fun, PrologAst},
    var_as_recexpr,
};

pub fn mk_deduce_rules(pbl: &Problem) -> impl Iterator<Item = PrologRule<Lang>> + use<'_> {
    chain! {
      mk_special_deduce_rules(pbl),
      mk_regular_deduce_rules(pbl),
      mk_exists_deduce_rules(pbl),
    }
}

// =========================================================
// ==================== special rules ======================
// =========================================================

/// Generate hard coded rules described
fn mk_special_deduce_rules(pbl: &Problem) -> impl Iterator<Item = PrologRule<Lang>> + use<'_> {
    let cleaned = clean_input(include_str!("base_deduce"))
        // rebuild a string without comments
        .split('.')
        .map(|x| x.trim().to_owned())
        .collect_vec(); // we need to collect here to force the iterator to take ownership

    cleaned
        .into_iter()
        .filter(|s| !s.is_empty())
        .inspect(|s| {
            dbg!(s);
        }) // uncomment to debug
        .map(|s| s.parse().unwrap())
        .map(move |patt: PrologAst<SymbolLang>| {
            patt.convert(|s| convert_fun(pbl, s)).unwrap().into_prolog()
        })
}

// =========================================================
// ===================== base rules ========================
// =========================================================

/// Generate the base deduce rule:
///
/// ```text
/// u, v |> x0, y0 # h, h'  ...  u, v |> xn, yn # h, h'
/// ---------------------------------------------------
///     u, v |> f(x0,...,xn), f(y0,...,yn) # h, h'
/// ```
///
/// for all "regular" `f`s
fn mk_regular_deduce_rules(pbl: &Problem) -> impl Iterator<Item = PrologRule<Lang>> + use<'_> {
    pbl.function
        .iter()
        .filter(|x| should_process_normaly(x))
        .map(mk_deduce_rule)
}

static HAS_SPECIAL_TREATMENT: FunctionFlags =
    const_fun_flags!(ALIAS | PROLOG_ONLY | MACRO | UNFOLD | CUSTOM_DEDUCE | EXISTS | SKOLEM);

fn should_process_normaly(f: &Function) -> bool {
    f.flags.intersects(HAS_SPECIAL_TREATMENT)
}

fn mk_deduce_rule(f: &Function) -> PrologRule<Lang> {
    assert!(should_process_normaly(f));
    let n: u32 = f.arity().try_into().unwrap();
    let s = f.signature.output;

    let vars @ [u, v, h1, h2] = [0, 1, 2, 3].map(Var::from_u32);
    let left_vars = (4..(4 + n)).map(Var::from_u32).collect_vec();
    let right_vars = ((4 + n)..(4 + 2 * n)).map(Var::from_u32).collect_vec();

    let input = mk_input(f, s, vars, &left_vars);
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
    fun_vars: &[Var],
) -> Pattern<logic_formula::egg::SimplLang<Function>> {
    let left = f.app_var(&var_as_recexpr(fun_vars));
    let right = f.app_var(&var_as_recexpr(fun_vars));
    let vars = var_as_recexpr(&vars);
    let ast: RecExpr<LangVar> = get_deduce(s).expect("unsupported sort").app_var(&[
        vars[0].as_slice(),
        &vars[1],
        &left,
        &right,
        &vars[2],
        &vars[3],
    ]);
    Pattern::new(ast)
}

const fn get_deduce(s: Sort) -> Option<&'static Function> {
    match s {
        Sort::Bool => Some(&BOOL_DEDUCE),
        Sort::Bitstring => Some(&BIT_DEDUCE),
        _ => return None,
    }
}

/// this generate `u,v|>a, b#h1, h2` using the right sort
///
/// `vars` is [u, v, a, b, h1, h2]
fn mk_dep(vars: [Var; 6], s: Sort) -> Option<Pattern<Lang>> {
    let vars = var_as_recexpr(&vars);
    let ast = get_deduce(s)?.app_var(&vars);
    Some(Pattern::new(ast))
}

// =========================================================
// ==================== exists rules =======================
// =========================================================
// QUESTION: Should we cross reference existential quantifiers?

fn mk_exists_deduce_rules(pbl: &Problem) -> impl Iterator<Item = PrologRule<Lang>> + use<'_> {
    debug_assert!(pbl.function.valid());
    pbl.function
        .quantifiers()
        .iter()
        .map(|q| mk_exists_deduce_rules_one(pbl, q))
}

/// Generate the rule for a single quantifier
fn mk_exists_deduce_rules_one(
    pbl: &Problem,
    Exists {
        tlf,
        skolem,
        fresh,
        ..
    }: &Exists,
) -> PrologRule<Lang> {
    let [tlf, skolem, fresh] = [tlf, skolem, fresh].map(|i| &pbl.function[*i]);
    let deduce = get_deduce(Sort::Bitstring).unwrap();
    let n: u32 = skolem.arity().try_into().unwrap();

    // initiate the variables
    let left_vars;
    let right_vars;
    let [u, v, h1, h2, il, ir] = {
        let f = |i| [ENodeOrVar::Var::<Lang>(Var::from_u32(i))];
        let vars = core::array::from_fn(|i| f(i as u32));
        let k = vars.len() as u32;
        left_vars = (k..(k + n)).map(&f).collect_vec();
        right_vars = ((k + n)..(k + 2 * n)).map(&f).collect_vec();
        vars
    };

    // u, v |> exits(vecx, il), exists(vecy, ir) # h1, h2
    let input = {
        let left = tlf.app_var(
            &chain!(left_vars.iter().map(|x| x.as_slice()), [il.as_slice()]).collect_vec(),
        );
        let right = tlf.app_var(
            &chain!(right_vars.iter().map(|x| x.as_slice()), [ir.as_slice()]).collect_vec(),
        );
        deduce.app_var(
            &chain![
                [u.as_slice(), v.as_slice()],
                [left.deref(), right.deref()],
                [h1.as_slice(), h2.as_slice()]
            ]
            .collect_vec(),
        )
    };

    // u, v |> exits(vecx, fresh), exists(vecy, fresh) # h1, h2
    let dep = {
        let fresh: PatternAst<Lang> = fresh.app_var::<3, [LangVar; 0]>(&[]);
        let left = tlf.app_var(
            &chain!(left_vars.iter().map(|x| x.as_slice()), [fresh.deref()]).collect_vec(),
        );
        let right = tlf.app_var(
            &chain!(right_vars.iter().map(|x| x.as_slice()), [fresh.deref()]).collect_vec(),
        );
        deduce.app_var(
            &chain![
                [u.as_slice(), v.as_slice()],
                [left.deref(), right.deref()],
                [h1.as_slice(), h2.as_slice()]
            ]
            .collect_vec(),
        )
    };

    PrologRule {
        input: Pattern::from(input),
        deps: vec![Pattern::from(dep)],
        cut: false,
        require_decrease: false,
        name: Some(format!("deduce {}", tlf.name)),
    }
}
