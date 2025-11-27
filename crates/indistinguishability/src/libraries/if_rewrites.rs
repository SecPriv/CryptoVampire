use egg::{Analysis, Pattern, Rewrite};
use itertools::{Itertools, chain, izip};
use utils::dynamic_iter;

use crate::terms::{
    AND, BITE, CONS_FA_BITSTRING, CONS_FA_BOOL, EQ, Function, IMPLIES, MITE, NOT, OR,
};
use crate::{Lang, Problem, rexp};

pub fn mk_rewrite<N: Analysis<Lang>>(pbl: &Problem) -> impl Iterator<Item = egg::Rewrite<Lang, N>> {
    chain![mk_static_rewrites(), mk_commute_if(pbl)]
}

fn mk_static_rewrites<N: Analysis<Lang>>() -> impl Iterator<Item = egg::Rewrite<Lang, N>> {
    let b_ite = &BITE;
    let m_ite = &MITE;
    decl_vars![a, b, c, d, v1, x, v];

    mk_many_rewrites! {
      ["if true"] (m_ite true #a #b) => (#a).
      ["if false"] (m_ite false #a #b) => (#b).
      ["if simp1"] (m_ite #x #a #a) => (#a).
    //   ["if simp2"] (m_ite #a #a false) => (#a).
      ["if simp3"] (m_ite #a (m_ite #a #b #c) #d) => (m_ite #a #b #d).
    //   ["if simp4"] (m_ite #a true false) => (#a).
      ["if eq1"] (m_ite (= #a #b) #a #b) => (#a).
      ["if eq2"] (m_ite (= #a #b) #a #b) => (#b).

      ["b_if true"] (b_ite true #a #b) => (#a).
      ["b_if false"] (b_ite false #a #b) => (#b).
      ["b_if simp1"] (b_ite #x #a #a) => (#a).
      ["b_if simp2"] (b_ite #a #a false) => (#a).
      ["b_if simp4"] (b_ite #a true false) => (#a).
      ["b_if simp3"] (b_ite #a (b_ite #a #b #c) #d) => (b_ite #a #b #d).

      ["if implies simp"] (b_ite (and #a #b) #a true) => true.
      ["if implies simp2"] (b_ite #a #a true) => true.
      ["if implies trans"] (#v1 = true, #v1 = (b_ite #a #b true), #v1 = (b_ite #b #c true)) => (#v1 = (=> #a #c)).
    }.into_iter()
}

fn mk_commute_if<N: Analysis<Lang>>(pbl: &Problem) -> impl Iterator<Item = egg::Rewrite<Lang, N>> {
    dynamic_iter!(ME; Empty:A, Many:B);

    if !pbl.config.if_commute {
        return ME::Empty(::std::iter::empty());
    }

    static FORBIDDEN: [&Function; 9] = [
        &MITE,
        &BITE,
        &AND,
        &IMPLIES,
        &NOT,
        &OR,
        &EQ,
        &CONS_FA_BITSTRING,
        &CONS_FA_BOOL,
    ];
    decl_vars!(const C:Bool);

    ME::Many(
        pbl.functions()
            .iter_current()
            .filter_map(|f| f.signature.output.get_if().map(|ite| (ite, f)))
            .filter(|(_, f)| f.is_part_of_F() && !FORBIDDEN.contains(f))
            .flat_map(move |(ite, f)| {
                let mut ret = Vec::with_capacity(1 + f.arity());
                if f.args_sorts().all(|s| !s.is_base()) {
                    return ret.into_iter();
                }

                let v1 = f.signature.mk_vars_expr().collect_vec();
                let v2 = f.signature.mk_vars_expr().collect_vec();

                {
                    let args1 = v1.iter().cloned();
                    let args2 = izip!(f.args_sorts(), &v2, &v1)
                        .map(|(s, v1, v2)| if s.is_base() { v1 } else { v2 })
                        .cloned();
                    let args3 = izip!(f.args_sorts(), &v1, &v2).map(|(s, v1, v2)| {
                        if let Some(ite) = s.get_if() {
                            rexp!((ite #C #v1 #v2))
                        } else {
                            rexp!(#v1)
                        }
                    });

                    let from = rexp!((ite #C (f #args1*) (f #args2*)));
                    let to = rexp!((f #args3*));

                    ret.push(
                        Rewrite::new(
                            format!("if commute {f}"),
                            Pattern::from(&from),
                            Pattern::from(&to),
                        )
                        .unwrap(),
                    );
                }

                {
                    // let args1 = v1.clone();
                    // let args2 = args1.clone();
                    // let args3 = args1.clone();

                    for (i, arg_ite) in f
                        .args_sorts()
                        .enumerate()
                        .filter_map(|(i, s)| s.get_if().map(|f| (i, f)))
                    {
                        let args1 = v1.iter().enumerate().map(|(j, v1)| {
                            if i == j {
                                rexp!((arg_ite #C #v1 #(v2[i].clone())))
                            } else {
                                v1.clone()
                            }
                        });
                        let args2 = v1.iter().cloned();
                        let args3 = v1
                            .iter()
                            .enumerate()
                            .map(|(j, v1)| if i == j { &v2[i] } else { v1 })
                            .cloned();

                        let from = rexp!((f #args1*));
                        let to = rexp!((ite #C (f #args2*) (f #args3*)));

                        ret.push(
                            Rewrite::new(
                                format!("if commute {f} <- #{i:}"),
                                Pattern::from(&from),
                                Pattern::from(&to),
                            )
                            .unwrap(),
                        );
                    }
                }

                ret.into_iter()
            }),
    )
}
