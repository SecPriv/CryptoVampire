//! This module implements high order terms. see [this
//! blog](https://web.archive.org/web/20240814030029/https://pavpanchekha.com/blog/egg-bindings.html#expand)
//! for more info

use egg::{Analysis, Pattern, Rewrite};
use itertools::chain;
use utils::econtinue_if;

use crate::libraries::Library;
use crate::terms::{Formula, Function, LAMBDA_S};
use crate::{Lang, Problem, rexp};

// static LET: Function = LAMBDA_LET.const_clone();
static S: Function = LAMBDA_S.const_clone();

use crate::libraries::utils::EggRewriteSink;

/// Creates rewrite rules for lambda calculus.
pub struct LambdaLib;

impl Library for LambdaLib {
    fn add_egg_rewrites<N: Analysis<Lang>>(
        &self,
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
        add_base_rw(sink);
        add_s_rw(pbl, sink);
    }
}

fn add_base_rw<N: Analysis<Lang>>(_sink: &mut impl EggRewriteSink<N>) {
    // decl_vars![x, y, m, hd, tl,  a, b, c, var];
    // mk_many_rewrites! {
    //   ["λlet subst"]
    //   (LET #var #m #var) => (#m).

    //   ["λlet skip"]
    //   (LET O #m (S #x)) => (S #x).

    // //   ["λlet simpl"]
    // //   (LET (S #y) #m (S #x)) => (LET #y #m #x).

    // //   ["λadd many s cons"]
    // //   (ADD_S (CONS #hd #tl) #m) => (S (ADD_S #tl #m)).

    // //   ["λadd many s nil"]
    // //   (ADD_S NIL #m) => (#m).

    // //   ["λlet exist"]
    // //   (LET #var #m (EXISTS (CONS #hd NIL) #a)) =>
    // //     (EXISTS (CONS #hd NIL) (LET (S (ADD_S NIL #var)) #m #a)).

    // //   ["λlet find"]
    // //   (LET #var #m (FIND_SUCH_THAT (CONS #hd NIL) #a #b #c)) =>
    // //     (FIND_SUCH_THAT (CONS #hd NIL)
    // //         (LET (S (ADD_S NIL #var)) #m #a)
    // //         (LET (S (ADD_S NIL #var)) #m #b)
    // //         (LET #var #m #c)).
    // }
    // .into_iter()
}

fn add_s_rw<N: Analysis<Lang>>(pbl: &Problem, sink: &mut impl EggRewriteSink<N>) {
    for f in pbl.functions().iter_current() {
        econtinue_if!(f.is_out_of_term_algebra());

        let vars = f.signature.mk_vars();
        let vars = vars.iter().map(|x| Formula::Var(x.clone()));
        let svars = vars.clone().map(|v| rexp!((S #v)));

        let searcher = Pattern::from(&rexp!((S (f #vars*))));
        let applier = Pattern::from(&rexp!((f #svars*)));
        sink.add_egg_rewrite(Rewrite::new(format!("λ S commutes {f}"), searcher, applier).unwrap());
    }
}

// fn mk_let_rw<N: Analysis<Lang>>(
//     pbl: &Problem,
// ) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
//     let m = fresh!();
//     let mvars = fresh!();
//     pbl.functions()
//         .iter_current()
//         .filter(|f| !f.is_out_of_term_algebra())
//         .map({
//             move |f| {
//                 let m = &m;
//                 let mvars = &mvars;
//                 let vars = f.signature.mk_vars();
//                 let vars = vars.iter().map(|x| RecFOFormula::Var(x.clone()));
//                 let svars = vars.clone().map(|v| rexp!((LET #mvars #m  #v)));

//                 let searcher = Pattern::from(&rexp!((LET #mvars #m (f #vars*))));
//                 let applier = Pattern::from(&rexp!((f #svars*)));

//                 Rewrite::new(format!("λ let commutes {f}"), searcher, applier).unwrap()
//             }
//         })
// }
