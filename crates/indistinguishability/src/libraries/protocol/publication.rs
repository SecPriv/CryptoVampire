use egg::{Analysis, Pattern};
use itertools::{Itertools, chain};
use utils::econtinue_if;

use crate::protocol::Step;
use crate::terms::{Function, HAPPENS, INIT, LT, MACRO_EXEC, MACRO_MSG};
use crate::{Lang, MSmt, Problem, fresh, rexp, smt};

pub fn mk_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = egg::Rewrite<Lang, N>> {
    let (pub_steps, steps): (Vec<_>, Vec<_>) =
        pbl.steps().unwrap().partition(|s| s.is_publish_step());

    let mut res = Vec::new();
    decl_vars!(p:Protocol);

    for s in pub_steps {
        econtinue_if!(s == INIT);
        assert!(s.is_publish_step());

        let vars = s.args_sorts().map(|x| fresh!(x).as_formula());
        let sf = rexp!((s #vars*));

        let order = steps.iter().map(|so| {
            let ovars = so.args_sorts().map(|x| fresh!(x).as_formula());
            let name = format!("publication ordering {s}, {so}");
            egg::Rewrite::new(
                name,
                Pattern::from(&rexp!((LT #sf (so #ovars*)))),
                Pattern::from(&rexp!(true)),
            )
            .unwrap()
        });

        let msg = {
            pbl.protocols().iter().map(|p| {
                let Step { vars, msg, .. } =
                    &pbl.protocols().first().unwrap().steps()[s.get_step_index().unwrap()];
                let vars = vars.iter().map(|x| x.as_formula());
                let p = p.name();
                egg::Rewrite::new(
                    format!("{s} msg macro in {p}"),
                    Pattern::from(msg),
                    Pattern::from(&rexp!((MACRO_MSG (s #(vars.clone())*) p))),
                )
                .unwrap()
            })
        };

        let exec = egg::Rewrite::new(
            format!("{s} exec macro"),
            Pattern::from(&rexp!((MACRO_EXEC #sf #p))),
            Pattern::from(&rexp!((HAPPENS #sf))),
        )
        .unwrap();
        res.extend(chain!([exec], msg, order));
    }

    res.into_iter()
}

use cryptovampire_smt::SmtSink;

use crate::MSmtParam;

pub fn add_smt(pbl: &Problem, sink: &mut impl SmtSink<MSmtParam>) {
    let (pub_steps, steps): (Vec<_>, Vec<_>) =
        pbl.steps().unwrap().partition(|s| s.is_publish_step());

    sink.extend_one_smt(MSmt::comment_block("Publication Steps"));

    for s in pub_steps {
        econtinue_if!(s == INIT);

        let vars = s.args_sorts().map(|x| fresh!(x)).collect_vec();
        let vars_iter = || vars.iter().cloned();
        let sf = smt!((s #(vars_iter())*));

        sink.comment(format!("step {s}"));

        sink.assert_one(smt!((forall ((#p Protocol)) (forall #(vars_iter()) (= (MACRO_EXEC #sf #p) (HAPPENS #sf))))));

        for so in steps.iter() {
            let ovars = so.args_sorts().map(|x| fresh!(x)).collect_vec();
            let ovars_iter = || ovars.iter().cloned();
            let all_vars = vars_iter().chain(ovars_iter());
            // sf is captured from outside.
            sink.assert_one(smt!((forall #all_vars (LT #sf (so #(ovars_iter())*)))));
        }
    }
}
