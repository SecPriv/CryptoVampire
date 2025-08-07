//! This module implements high order terms. see [this
//! blog](https://web.archive.org/web/20240814030029/https://pavpanchekha.com/blog/egg-bindings.html#expand)
//! for more info

use egg::{Analysis, ENodeOrVar, Pattern, Rewrite, Var};
use itertools::Itertools;
use logic_formula::egg::SimpleDiscriminant;

use crate::terms::{Function, LAMBDA_LET, LAMBDA_O, LAMBDA_S};
use crate::{Lang, Problem, rexp};

static LET: Function = LAMBDA_LET.const_clone().unwrap();
static S: Function = LAMBDA_S.const_clone().unwrap();
static O: Function = LAMBDA_O.const_clone().unwrap();

fn mk_base_rw<N: Analysis<Lang>>() -> impl Iterator<Item = Rewrite<Lang, N>> {
    decl_vars![x, m];
    mk_many_rewrites! {
      ["λlet subst"]
      (LET #m O) => (#m).

      ["λlet skip"]
      (LET #m (S #x)) => (#x).
    }
    .into_iter()
}

fn mk_s_rw<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.function
        .iter()
        .filter(|f| f.is_out_of_term_algebra())
        .map(|f| {
            let vars = f
                .signature
                .mk_egg_vars(0)
                .map(|x| [ENodeOrVar::Var(x)])
                .collect_vec();
            let svars = f
                .signature
                .mk_egg_vars(0)
                .map(ENodeOrVar::Var)
                .map(|x| rexp!((S #x)))
                .collect_vec();

            let searcher: Pattern<_> = S.app_var(&[f.app_var(&vars)]).into();
            let applier: Pattern<_> = f.app_var(&svars).into();

            Rewrite::new(format!("λ S commutes {f}"), searcher, applier).unwrap()
        })
}

fn mk_let_rw<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    decl_vars!(N; y);
    pbl.function
        .iter()
        .filter(|f| f.is_out_of_term_algebra())
        .map(move |f| {
            let vars = f
                .signature
                .mk_egg_vars(N)
                .map(|x| [ENodeOrVar::Var(x)])
                .collect_vec();
            let svars = f
                .signature
                .mk_egg_vars(N)
                .map(ENodeOrVar::Var)
                .map(|x| rexp!((LET #y #x)))
                .collect_vec();

            let searcher: Pattern<_> = LET
                .app_var(&[[y.clone()].as_slice(), &f.app_var(&vars)])
                .into();
            let applier: Pattern<_> = f.app_var(&svars).into();

            Rewrite::new(format!("λ let commutes {f}"), searcher, applier).unwrap()
        })
}
