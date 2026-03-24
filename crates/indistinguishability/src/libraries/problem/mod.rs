use cryptovampire_smt::SmtSink;
use egg::{Analysis, Pattern, PatternAst, Rewrite};
use itertools::chain;
use log::trace;
use utils::{econtinue_if, econtinue_let};

use crate::libraries::Library;
use crate::libraries::utils::EggRewriteSink;
use crate::terms::{AliasRewrite, Function};
use crate::{Lang, LangVar, MSmtParam, Problem, rexp, smt};

/// Creates rewrite rules based on the problem definition, including extra rewrite rules and alias rules.
fn add_rewrites<N: Analysis<Lang>>(pbl: &Problem, sink: &mut impl EggRewriteSink<N>) {
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

/// Generates SMT assertions for extra rewrite rules defined in the problem.
///
/// This iterates through rewrite rules that are not prolog-only and generates
/// corresponding SMT axioms.
fn add_extra_smt_rw(pbl: &Problem, sink: &mut impl SmtSink<MSmtParam>) {
    sink.reserve(2 + 2 * pbl.extra_rewrite().len());

    sink.comment_block("Cross engine rewrites");
    sink.comment("this include custom rewrites and library rewrites");

    for crate::terms::Rewrite {
        from,
        to,
        variables,
        prolog_only,
        name,
        ..
    } in pbl.extra_rewrite()
    {
        econtinue_if!(*prolog_only);
        let [from, to] = [from, to].map(|x| x.as_smt(pbl).unwrap());
        let vars = variables.clone().into_owned();

        if let Some(name) = name {
            sink.comment(name);
        }

        sink.assert_one(smt!((forall #vars (= #from #to))))
    }
}

pub struct ProblemLib;

impl Library for ProblemLib {
    fn add_static_egg_rewrites<N: Analysis<Lang>>(
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
        add_rewrites(pbl, sink);
    }

    fn add_dynamic_rules(pbl: &mut Problem, sink: &mut impl super::utils::RuleSink) {
        #[allow(deprecated)]
        sink.extend_rc_rules(pbl.extra_rules().iter().cloned());
    }

    fn add_smt(pbl: &mut Problem, sink: &mut impl SmtSink<MSmtParam>) {
        add_extra_smt_rw(pbl, sink);

        sink.comment_block("Custom smt");
        sink.extend_smt(pbl.extra_smt().iter().cloned());
    }
}
