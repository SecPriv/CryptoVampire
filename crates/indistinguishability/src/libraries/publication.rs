use egg::{Analysis, Pattern};
use itertools::{Itertools, chain};
use utils::econtinue_if;

use crate::terms::{Function, HAPPENS, INIT, LT, MACRO_EXEC};
use crate::{Lang, MSmt, Problem, fresh, rexp, smt};

fn public_steps(pbl: &Problem) -> impl Iterator<Item = Function> {
    pbl.steps().unwrap().filter(|s| s.is_publish_step())
}

pub fn mk_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = egg::Rewrite<Lang, N>> {
    let (pub_steps, steps): (Vec<_>, Vec<_>) =
        pbl.steps().unwrap().partition(|s| s.is_publish_step());

    let mut res = Vec::new();
    decl_vars!(p:Protocol);

    for s in pub_steps {
        econtinue_if!(s == INIT);

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

        let exec = egg::Rewrite::new(
            format!("{s} exec macro"),
            Pattern::from(&rexp!((MACRO_EXEC #p #sf ))),
            Pattern::from(&rexp!((HAPPENS #sf))),
        )
        .unwrap();
        res.extend(chain!([exec], order));
    }

    res.into_iter()
}

pub fn mk_smt(pbl: &Problem) -> impl Iterator<Item = MSmt> {
    let (pub_steps, steps): (Vec<_>, Vec<_>) =
        pbl.steps().unwrap().partition(|s| s.is_publish_step());

    let mut res = vec![MSmt::comment_block("Publication Steps")];
    decl_vars!(p:Protocol);

    for s in pub_steps {
        econtinue_if!(s == INIT);

        let vars = s.args_sorts().map(|x| fresh!(x));
        let sf = smt!((s #vars*));

        let comment = MSmt::Comment(format!("step {s}"));
        let order = steps
            .iter()
            .map(|so| {
                let ovars = so.args_sorts().map(|x| fresh!(x));
                smt!((LT #sf (so #ovars*)))
            })
            .map(MSmt::Assert);

        let exec = MSmt::Assert(
            smt!((= (MACRO_EXEC #p #sf) (HAPPENS #sf))));
        res.extend(chain!([comment, exec], order));
    }

    res.into_iter()
}
