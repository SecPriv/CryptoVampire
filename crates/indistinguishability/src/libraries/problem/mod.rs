use egg::{Analysis, Pattern, PatternAst, Rewrite};
use itertools::chain;
use log::trace;
use utils::{econtinue_if, econtinue_let};

use crate::libraries::utils::EggRewriteSink;
use crate::terms::{AliasRewrite, Function};
use crate::{Lang, LangVar, Problem, rexp};

/// Creates rewrite rules based on the problem definition, including extra rewrite rules and alias rules.
pub fn add_rewrites<N: Analysis<Lang>>(pbl: &Problem, sink: &mut impl EggRewriteSink<N>) {
    add_extra_rw_rules(pbl, sink);
    add_alias_rule(pbl, sink);
}

fn add_extra_rw_rules<N: Analysis<Lang>>(pbl: &Problem, sink: &mut impl EggRewriteSink<N>) {
    let iter = pbl.extra_rewrite().iter().enumerate().map(
        |(i, crate::terms::Rewrite { from, to, name, .. })| {
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
        },
    );
    sink.extend_egg_rewrites(iter);
}

fn add_alias_rule<N: Analysis<Lang>>(pbl: &Problem, sink: &mut impl EggRewriteSink<N>) {
    for f in pbl.functions().iter_current() {
        econtinue_let!(let Some(a) = &f.alias);
        sink.reserve(a.len());
        for (i, rw) in a.iter().enumerate() {
            sink.add_egg_rewrite(mk_alias_rule_1(i, f, rw));
        }
    }
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
