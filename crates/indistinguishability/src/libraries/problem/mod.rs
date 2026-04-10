use egg::{Analysis, Pattern, PatternAst, Rewrite};
use itertools::chain;
use log::trace;
use utils::{econtinue_if, econtinue_let, ereturn_if};

use crate::libraries::Library;
use crate::libraries::utils::{EggRewriteSink, INDEPEDANT_QUERY, SmtSink};
use crate::problem::cache::Context;
use crate::terms::{AliasRewrite, Function};
use crate::{Lang, LangVar, MSmtParam, Problem, rexp, smt};

// TODO: delete once we are sure this has been properly replaced
#[allow(dead_code)]
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

pub struct ProblemLib;

impl Library for ProblemLib {
    fn add_egg_rewrites<N: Analysis<Lang>>(
        &self,
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
        // add_extra_rw_rules(pbl, sink);
        add_alias_rule(pbl, sink);
    }

    fn add_rewrites(&self, pbl: &mut Problem, sink: &mut impl super::utils::RewriteSink) {
        sink.extend_rewrites(pbl, pbl.extra_rewrite().iter().cloned());
    }

    fn add_rules(&self, pbl: &mut Problem, sink: &mut impl super::utils::RuleSink) {
        #[allow(deprecated)]
        sink.extend_rc_rules(pbl.extra_rules().iter().cloned());
    }

    fn add_smt<'a>(&self, pbl: &mut Problem, ctx: &Context, sink: &mut impl SmtSink<'a>) {
        ereturn_if!(ctx.using_cache);
        sink.comment_block(pbl, &INDEPEDANT_QUERY, "Custom smt");
        sink.extend_smt(pbl, &INDEPEDANT_QUERY, pbl.extra_smt().iter().cloned());
    }
}
