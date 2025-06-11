use egg::{Analysis, ENodeOrVar, Pattern, RecExpr, Rewrite, SymbolLang};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::egg::{SimplLang, SimpleDiscriminant};
use std::collections::HashMap;
use utils::impossible::Impossible;

use super::{
    parse::{PatternsAst, clean_input, convert_fun},
    var_as_recexpr,
};
use crate::{
    Configuration, Lang, LangVar, Problem,
    protocol::Protocol,
    terms::{Exists, Function, PARSING_PAIRS},
};
/// build the default rewrite rules
pub fn mk_rewrites_rules<N: Analysis<Lang> + 'static>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain! {
      manual_rules(pbl),
      exists_rules(pbl),
      unfold_rules(pbl)
    }
    .inspect(|rw| {
        if log::log_enabled!(log::Level::Trace) {
            trace!("rw: {rw:#?}")
        }
    })
}

fn unfold_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.protocols.iter().flat_map(|ptcl| {
        let steps = ptcl.steps();
        let ptcl = ptcl.name();
        steps.iter().flat_map(|s| s.mk_unfold_rewrites(ptcl))
    })
}

/// Rules added manualy in `builtin_rewrites`
fn manual_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    let cleaned = clean_input(include_str!("builtin_rewrites"))
        // rebuild a string without comments
        .split('.')
        .map(|x| x.trim().to_owned())
        .collect_vec(); // we need to collect here to force the iterator to take ownership

    cleaned
        .into_iter()
        .filter(|s| !s.is_empty())
        .inspect(|s| trace!("parsing {s}")) // uncomment to debug
        .map(|s| s.parse().unwrap())
        .map(move |patt: PatternsAst<SymbolLang>| {
            patt.convert(|s| convert_fun(pbl, s))
                .unwrap()
                .into_rewrite()
                .unwrap()
        })
}

fn exists_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.function
        .quantifiers()
        .iter()
        .flat_map(|e| mk_exists_rules_one(pbl, e))
}

fn mk_exists_rules_one<'a, N: Analysis<Lang>>(
    Problem { function, .. }: &'a Problem,
    Exists {
        vars,
        bound_var,
        patt,
        tlf,
        skolem,
        ..
    }: &'a Exists,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
    let def = {
        let vars = var_as_recexpr(chain!(vars, [bound_var]));
        Rewrite::new(
            format!("{} def", &tlf.name),
            Pattern::new(tlf.app_var(&vars)),
            Pattern::new(patt.clone()),
        )
        .unwrap()
    };

    // TODO: sound
    // let sound = {
    //     let skolem_args = var_as_recexpr(vars);
    //     let sk = skolem.app_var(&skolem_args);
    //     let tlf_args: Vec<_> =
    //         chain!(skolem_args.iter().map(|x| x.as_slice()), [sk.as_ref()]).collect();

    //     Rewrite::new(
    //         format!("{} sound", &tlf.name),
    //         Pattern::new(tlf.app_var(&tlf_args)),
    //         Pattern::new(patt.clone().apply_pattern_subst(vec![(*bound_var, sk)])),
    //     )
    //     .unwrap()
    // };

    // chain![[def, sound]]
    chain![[def]]
}
