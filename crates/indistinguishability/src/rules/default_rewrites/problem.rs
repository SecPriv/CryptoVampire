
use egg::{Analysis, Pattern, Rewrite, SymbolLang};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::egg::SimpleDiscriminant;
use utils::dynamic_iter;

// use super::parse::{PatternsAst, clean_input, convert_fun};
// use super::var_as_recexpr;
use crate::terms::{
    AliasRewrite, BITE, Exists, FindSuchThat, Function, MITE, Quantifier, QuantifierT,
};
use crate::{Lang, Problem};

pub fn mk_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
  chain![
    unfold_rules(pbl),
    mk_extra_rw_rules(pbl),
    mk_alias_rule(pbl)
  ]
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