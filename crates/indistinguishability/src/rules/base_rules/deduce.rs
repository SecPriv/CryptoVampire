use egg::{ENodeOrVar, Pattern, PatternAst, RecExpr, SymbolLang, Var};
use golgge::PrologRule;
use itertools::{chain, izip, Itertools};
use logic_formula::egg::SimpleDiscriminant;
use utils::implvec;

use crate::{
    terms::{Function, FunctionFlags, Sort, BIT_DEDUCE, BOOL_DEDUCE},
    Lang, LangVar, Problem,
};

use super::parse::{clean_input, convert_fun, PrologAst};

pub fn mk_deduce_rules(pbl: &Problem) -> impl Iterator<Item = PrologRule<Lang>> + use<'_> {
    chain! {
      mk_special_deduce_rules(pbl),
      mk_regular_deduce_rules(pbl),
    }
}

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

/// helper to write flags
macro_rules! f {
    ($id:ident) => {FunctionFlags::$id};
    ($id0:ident | $($id:ident)|*) => {
        FunctionFlags::$id0
            $(.union(FunctionFlags::$id))*
    };
}

static HAS_SPECIAL_TREATMENT: FunctionFlags =
    f!(ALIAS | PROLOG_ONLY | MACRO | UNFOLD | CUSTOM_DEDUCE);

fn mk_regular_deduce_rules(
    pbl: &Problem,
) -> impl Iterator<Item = PrologRule<Lang>> + use<'_> {
    pbl.function
        .iter()
        .filter(|x| should_process_normaly(x))
        .map(mk_deduce_rule)
}

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

fn get_deduce(s: Sort) -> Option<&'static Function> {
    match s {
        Sort::Bool => Some(&BOOL_DEDUCE),
        Sort::Bitstring => Some(&BIT_DEDUCE),
        _ => return None,
    }
}

fn var_as_recexpr<'a, L>(vars: implvec!(&'a Var)) -> Vec<[ENodeOrVar<L>; 1]> {
    vars.into_iter()
        .copied()
        .map(ENodeOrVar::Var)
        .map(|x| [x])
        .collect()
}

/// this generate `u,v|>a, b#h1, h2` using the right sort
///
/// `vars` is [u, v, a, b, h1, h2]
fn mk_dep(vars: [Var; 6], s: Sort) -> Option<Pattern<Lang>> {
    let vars = var_as_recexpr(&vars);
    let ast = get_deduce(s)?.app_var(&vars);
    Some(Pattern::new(ast))
}
