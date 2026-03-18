use egg::{Analysis, Pattern, PatternAst, Rewrite};
use itertools::chain;
use log::trace;

use crate::terms::{AliasRewrite, Function};
use crate::{Lang, LangVar, Problem, rexp};

/// Creates rewrite rules based on the problem definition, including extra rewrite rules and alias rules.
pub fn mk_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain![mk_extra_rw_rules(pbl), mk_alias_rule(pbl)]
}

fn mk_extra_rw_rules<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.extra_rewrite()
        .iter()
        .enumerate()
        .map(|(i, crate::terms::Rewrite { from, to, name, .. })| {
            let name = name
                .as_ref()
                .cloned()
                .unwrap_or_else(|| format!("extra rewrite #{i:}").into())
                .into_owned();
            trace!("registering rw rule {name} to egg...");

            let from = from.as_egg_non_capture_avoiding::<LangVar>();
            Rewrite::new(
                name,
                Pattern::from(PatternAst::from(from)),
                Pattern::from(to),
            )
            .unwrap()
        })
}

fn mk_alias_rule<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.functions()
        .iter_current()
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
        Pattern::from(&rexp!((f #(from.iter().cloned())*))),
        Pattern::from(to),
    )
    .unwrap()
}
