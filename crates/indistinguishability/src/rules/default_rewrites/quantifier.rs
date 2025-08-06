use egg::{Analysis, Pattern, Rewrite, SymbolLang};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::egg::SimpleDiscriminant;
use utils::dynamic_iter;

use crate::rules::var_as_recexpr;
use crate::terms::{
    AliasRewrite, BITE, Exists, FindSuchThat, Function, MITE, Quantifier, QuantifierT,
};
use crate::{Lang, Problem};

pub fn mk_rewrites<N: Analysis<Lang>>(
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
