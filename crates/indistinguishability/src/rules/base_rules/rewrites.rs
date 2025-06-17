use egg::{Analysis, Pattern, Rewrite, SymbolLang};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::egg::SimpleDiscriminant;

use super::{
    parse::{PatternsAst, clean_input, convert_fun},
    var_as_recexpr,
};
use crate::{
    Lang, Problem,
    terms::{AliasRewrite, Exists, Function},
};
/// build the default rewrite rules
pub fn mk_rewrites_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain! {
      manual_rules(pbl),
      exists_rules(pbl),
      unfold_rules(pbl),
      mk_alias_rule(pbl),
      mk_extra_rw_rules(pbl)
    }
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
    Problem {  .. }: &'a Problem,
    Exists {
        vars,
        bound_var,
        patt,
        tlf,
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

fn mk_extra_rw_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.extra_rewrite()
        .iter()
        .enumerate()
        .map(|(i, crate::terms::Rewrite { from, to, .. })| {
            Rewrite::new(
                format!("extra rewrite #{i:}"),
                Pattern::new(from.clone().into_owned().into()),
                Pattern::new(to.clone().into_owned().into()),
            )
            .unwrap()
        })
}

fn mk_alias_rule<N: Analysis<Lang>>(
    Problem { function, .. }: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    function
        .iter()
        .filter_map(|f| f.alias.as_ref().map(|a| (f, a)))
        .flat_map(|(f, a)| a.iter().enumerate().map(move |(i, rw)| (i, f, rw)))
        .map(|(i, f, rw)| mk_alias_rule_1(i, f, rw))
}

fn mk_alias_rule_1<N: Analysis<Lang>>(
    i: usize,
    f: &Function,
    AliasRewrite { from, to, .. }: &AliasRewrite,
) -> Rewrite<Lang, N> {
    Rewrite::new(
        format!("{} definition #{i:}", &f.name),
        Pattern::new(f.app_var(&from)),
        Pattern::new(to.clone().into_owned().into()),
    )
    .unwrap()
}
