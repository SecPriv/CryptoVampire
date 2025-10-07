//! This module implements high order terms. see [this
//! blog](https://web.archive.org/web/20240814030029/https://pavpanchekha.com/blog/egg-bindings.html#expand)
//! for more info

use egg::{Analysis, ENodeOrVar, Pattern, Rewrite, Var};
use itertools::{Itertools, chain};

use crate::terms::{
    ADD_S, CONS, EXISTS, FIND_SUCH_THAT, Function, LAMBDA_LET, LAMBDA_O, LAMBDA_S, NIL,
    RecFOFormula,
};
use crate::{Lang, Problem, fresh, rexp};

static LET: Function = LAMBDA_LET.const_clone();
static S: Function = LAMBDA_S.const_clone();
static O: Function = LAMBDA_O.const_clone();

pub fn mk_rewrites<N: Analysis<Lang>>(pbl: &Problem) -> impl Iterator<Item = Rewrite<Lang, N>> {
    chain![mk_base_rw::<N>(), mk_s_rw::<N>(pbl),]
}

fn mk_base_rw<N: Analysis<Lang>>() -> impl Iterator<Item = Rewrite<Lang, N>> {
    decl_vars![x, m, hd, tl, sorts, a, b, c];
    mk_many_rewrites! {
      ["λlet subst"]
      (LET #m O) => (#m).

      ["λlet skip"]
      (LET #m (S #x)) => (#x).

      ["λadd many s cons"]
      (ADD_S (CONS #hd #tl) #m) => (ADD_S #tl (S #m)).

      ["λadd many s nil"]
      (ADD_S NIL #m) => (#m).

      ["λlet exist"]
      (LET #m (EXISTS #sorts #a)) =>
        (EXISTS #sorts (LET #m (ADD_S #sorts #a))).

      ["λlet find"]
      (LET #m (FIND_SUCH_THAT #sorts #a #b #c)) =>
        (FIND_SUCH_THAT #sorts (LET #m (ADD_S #sorts #a)) (LET #m (ADD_S #sorts #b)) (LET #m #c)).
    }
    .into_iter()
}

fn mk_s_rw<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    pbl.functions()
        .iter_current()
        .filter(|f| f.is_out_of_term_algebra())
        .map(|f| {
            let vars = f.signature.mk_vars();
            let vars = vars.iter().map(|x| RecFOFormula::Var(x.clone()));
            let svars = vars.clone().map(|v| rexp!((S #v)));

            let searcher = Pattern::from(&rexp!((S (f #vars*))));
            let applier = Pattern::from(&rexp!((f #svars*)));

            Rewrite::new(format!("λ S commutes {f}"), searcher, applier).unwrap()
        })
}

fn mk_let_rw<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    let m = fresh!();
    pbl.functions()
        .iter_current()
        .filter(|f| f.is_out_of_term_algebra())
        .map({
            let m = &m;
            move |f| {
                let vars = f.signature.mk_vars();
                let vars = vars.iter().map(|x| RecFOFormula::Var(x.clone()));
                let svars = vars.clone().map(|v| rexp!((LET #m  #v)));

                let searcher = Pattern::from(&rexp!((LET #m (f #vars*))));
                let applier = Pattern::from(&rexp!((f #svars*)));

                Rewrite::new(format!("λ let commutes {f}"), searcher, applier).unwrap()
            }
        })
}
