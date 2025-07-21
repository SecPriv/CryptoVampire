use egg::{Analysis, Pattern, Rewrite, SymbolLang};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::egg::SimpleDiscriminant;
use utils::dynamic_iter;

use super::parse::{PatternsAst, clean_input, convert_fun};
use super::var_as_recexpr;
use crate::terms::{AliasRewrite, Exists, FindSuchThat, Function, Quantifier, QuantifierT, BITE, MITE};
use crate::{Lang, Problem};
/// build the default rewrite rules
pub fn mk_rewrites_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain! {
      manual_rules(pbl),
      quantifier_rules(pbl),
      unfold_rules(pbl),
      mk_alias_rule(pbl),
      mk_extra_rw_rules(pbl)
    }
}

fn unfold_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.protocols().iter().flat_map(|ptcl| {
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

fn quantifier_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    dynamic_iter!(Tmp; A:A, B:B);
    pbl.function.quantifiers().iter().flat_map(|e| match e {
        Quantifier::Exists(e) => Tmp::A(mk_exists_rules_one(pbl, e)),
        Quantifier::FindSuchThat(e) => Tmp::B(mk_fdst_rules_one(pbl, e)),
    })
}

fn mk_exists_rules_one<'a, N: Analysis<Lang>>(
    Problem { .. }: &'a Problem,
    e: &'a Exists,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
    let def = {
        let vars = var_as_recexpr(chain![e.cvars(), e.bvars()]);
        Rewrite::new(
            format!("{} def", e.top_level_function().name),
            Pattern::new(e.top_level_function().app_var(&vars)),
            e.patt().iter().cloned().collect::<Pattern<_>>(),
        )
        .unwrap()
    };

    // TODO: sound

    chain![[def]]
}

fn mk_fdst_rules_one<'a, N: Analysis<Lang>>(
    Problem { .. }: &'a Problem,
    e: &'a FindSuchThat,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
    let def = {
        let vars = var_as_recexpr(chain![e.cvars(), e.bvars()]);
        Rewrite::new(
            format!("{} def", e.top_level_function().name),
            Pattern::new(e.top_level_function().app_var(&vars)),
            Pattern::new(MITE.app_var(&[e.condition(), e.then_branch(), e.else_branch()])),
        )
        .unwrap()
    };

    // TODO: sound

    chain![[def]]
}

fn mk_extra_rw_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.extra_rewrite().iter().enumerate().map(
        |(i, crate::terms::Rewrite { from, to, name, .. })| {
            let name = name
                .as_ref()
                .cloned()
                .unwrap_or_else(|| format!("extra rewrite #{i:}").into())
                .into_owned();
            trace!("registering rw rule {name} to egg...");

            Rewrite::new(
                name,
                Pattern::new(from.clone().into_owned().into()),
                Pattern::new(to.clone().into_owned().into()),
            )
            .unwrap()
        },
    )
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
        Pattern::new(f.app_var(from)),
        Pattern::new(to.clone().into_owned().into()),
    )
    .unwrap()
}
