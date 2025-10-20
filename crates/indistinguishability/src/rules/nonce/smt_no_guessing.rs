use itertools::chain;
use log::trace;

use crate::protocol::Protocol;
use crate::rules::nonce::Nonce;
use crate::rules::utils::SyntaxSearcher;
use crate::rules::utils::fresh::RefFormulaBuilder;
use crate::terms::{Function, IS_INDEPENDANT_BITSTRING, MACRO_FRAME, NONCE, RecFOFormula, Sort};
use crate::{MSmt, MSmtFormula, Problem, rexp, smt};

pub fn mk_no_guessing_smt<'a>(pbl: &'a Problem) -> impl Iterator<Item = MSmt> + use<'a> {
    chain![
        [MSmt::Comment("no guessing theorem & co".into())],
        chain![
            [mk_no_guessing_theorem(), mk_smt_nonce(),],
            pbl.functions().iter_current().filter_map(mk_smt_fun_one),
            pbl.protocols().iter().map(|ptcl| mk_smt_step(pbl, ptcl))
        ]
        .map(MSmt::mk_assert)
    ]
}

fn mk_no_guessing_theorem() -> MSmtFormula {
    let indep = get_is_independant(Sort::Bitstring).unwrap();
    smt!((forall ((!n Nonce) (!m Bitstring))
        (=> (indep !n !m) (distinct (NONCE !n) !m))))
}

fn mk_smt_nonce() -> MSmtFormula {
    let indep = get_is_independant(Sort::Bitstring).unwrap();
    smt!((forall ((!n Nonce) (!k Nonce))
        (=> (distinct !n !k) (indep !n (NONCE !k)))))
}

fn mk_smt_fun_one(fun: &Function) -> Option<MSmtFormula> {
    if fun.is_special_subterm() || fun.is_should_not_declare_in_smt() || fun == &NONCE {
        None
    } else {
        mk_regular(fun)
    }
}

fn mk_regular(fun: &Function) -> Option<MSmtFormula> {
    let indep = get_is_independant(fun.signature.output)?;

    decl_vars!(x:Nonce);

    let vars = fun.signature.mk_vars();
    let vars = vars.iter();
    let premises = vars.clone().filter_map(|var| {
        let indep = get_is_independant(var.get_sort()?)?;
        Some(smt!((indep !x !var)))
    });

    let bvars = chain![[x], vars.clone()].cloned();
    let vars = vars.cloned().map(MSmtFormula::Var);
    Some(smt!((forall #bvars (=> (and #premises*) (indep !x (fun #vars*))))))
}

// fn mk_buitin_smt() -> impl Iterator<Item = MSmtFormula> {
//     use Sort::{Bool, Bitstring, Nonce};
//     // let indep_b = get_is_independant(Bool).unwrap();
//     // let indep_m = get_is_independant(Bitstring).unwrap();
//     // vec_smt!(
//     //     (forall ((#n!0 Nonce) (#x!1 Bool)) (=>  (indep_b #n #x) (indep_b #n (not #x)))),
//     //     (forall ((#n!0 Nonce) (#a!1 Bool) (#a!2 Bool))
//     //         (=>  (and (indep_b #n #a) (indep_b #n #b)) (indep_b #n (and #x #b)))),
//     //     (forall ((#n!0 Nonce) (#a!1 Bool) (#a!2 Bool))
//     //         (=>  (and (indep_b #n #a) (indep_b #n #b)) (indep_b #n (or #x #b)))),
//     // ).into_iter()

// }

fn mk_smt_step<'a>(pbl: &'a Problem, ptcl: &'a Protocol) -> MSmtFormula {
    decl_vars!(x:Nonce, t:Time);

    // search
    let nonce = Nonce::builder()
        .content(RecFOFormula::Var(x.clone()))
        .build();
    let builder = RefFormulaBuilder::builder().build();
    nonce.search_frame(pbl, &builder, ptcl, &rexp!(#t));

    // build formula
    let formula = builder
        .into_inner()
        .unwrap()
        .into_formula()
        .as_smt(pbl)
        .unwrap();
    let indep_m = get_is_independant(Sort::Bitstring).unwrap();
    let p = ptcl.name();
    let ret = smt!((forall #([x.clone(), t.clone()])
    (=> #formula (and
        (indep_m !x (MACRO_FRAME !t p))
        // (indep_b #x (MACRO_EXEC #t p))
    ))));

    // return
    trace!("no guessing ptcl:\n{ret}");
    ret
}

const fn get_is_independant(sort: Sort) -> Option<Function> {
    match sort {
        Sort::Bitstring => Some(IS_INDEPENDANT_BITSTRING.const_clone()),
        // Sort::Bool => IS_INDEPENDANT_BOOL.const_clone(),
        _ => None,
    }
}
