use std::u32;

use cryptovampire_macros::smt;
use cryptovampire_smt::{IntoSmt, SortedVar};
use egg::Var;
use itertools::{chain, Itertools};
use log::trace;

use crate::{
    protocol::{Protocol, Step}, rules::{nonce::Nonce, utils::{fresh::RefFormulaBuilder, SyntaxSearcher}}, terms::{formula_utils::{offset_rexpr_owned, offset_var}, Function, RecFOFormula, Sort, HAPPENS, IS_INDEPENDANT_BITSTRING, LT, MACRO_FRAME, NONCE}, MSmt, MSmtFormula, Problem
};


pub fn mk_no_guessing_smt<'a>(pbl:&'a Problem) -> impl Iterator<Item = MSmt> + use<'a> {
    chain![
        [MSmt::Comment("no guessing theorem & co".into())],
        chain![
            [
                mk_no_guessing_theorem(),
                mk_smt_nonce(),
            ],
            pbl.function.iter().filter_map(mk_smt_fun_one),
            pbl.protocols().iter().map(|ptcl| mk_smt_step(pbl, ptcl))
        ].map(MSmt::mk_assert)
    ]
}

fn mk_no_guessing_theorem() -> MSmtFormula {
    use Sort::{Nonce, Bitstring};
    let indep = get_is_independant(Bitstring).unwrap();
    smt!((forall ((#n!0 Nonce) (#m!1 Bitstring))
        (=> (indep #n #m) (distinct (NONCE #n) #m))))
}

fn mk_smt_nonce() -> MSmtFormula {
    use Sort::Nonce;
    let indep = get_is_independant(Sort::Bitstring).unwrap();
    smt!((forall ((#n!0 Nonce) (#k!1 Nonce))
        (=> (distinct #n #k) (indep #n (NONCE #k)))))
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

    let vars = fun.signature.mk_sorted_vars(1);
    let premises = vars.clone().filter_map(|var @ SortedVar { sort, .. }| {
        let indep = get_is_independant(sort)?;
        Some(smt!((indep #0 #var)))
    });

    Some(smt!((forall ((#x!0 Sort::Nonce)) (forall #(vars.clone().collect()) 
        (=> (and #premises*) (indep #x (fun #vars*)))))))
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


fn mk_smt_step<'a>(pbl:&'a Problem, ptcl: &'a Protocol) -> MSmtFormula {
    let indep_m = get_is_independant(Sort::Bitstring).unwrap();
    let p =ptcl.name();
    let indices@[xi, ti] = ::std::array::from_fn(|i| i as u32);
    let [x, t] = indices.map(Var::from_u32);
    let nonce = Nonce::builder().content(RecFOFormula::Var(x)).build();
    let n = 2;


        let builder = RefFormulaBuilder::builder().and().min_var(n).build();

        for Step {
            id,
            vars,
            cond,
            msg,
        } in ptcl.steps()
        {
            let vars = vars.iter().map(|v| offset_var(n, *v)).collect_vec();
            let cond = offset_rexpr_owned(n, cond.iter().cloned());
            let msg = offset_rexpr_owned(n, msg.iter().cloned());

            // build the condition object
            let condition = {
                let named = id.rapp(vars.iter().cloned().map(RecFOFormula::Var));
                let happend_cond = HAPPENS.rapp([named.clone()]);
                let lt_cond = LT.rapp([named.clone(), RecFOFormula::Var(t)]);

                happend_cond & lt_cond
            };

            let builder =
                builder.add_node().and().forall()
                    .condition(condition)
                    .variables(vars)
                    .sorts(id.signature.inputs_iter())
                    .build();
            nonce.inner_search_recexpr(pbl, &builder, &cond);
            nonce.inner_search_recexpr(pbl, &builder, &msg);
        }
        let formula = builder.into_inner().unwrap().into_formula().into_smt();

        let [x, t] = [SortedVar::new(xi, Sort::Nonce), SortedVar::new(ti, Sort::Time)];
        let vars = vec![x.clone(), t.clone()];

        let ret = smt!((forall #vars 
                (=> #formula (and 
                    (indep_m #x (MACRO_FRAME #t p)) 
                    // (indep_b #x (MACRO_EXEC #t p))
                ))));
                trace!("no guessing ptcl:\n{ret}");
                ret
}



const fn get_is_independant(sort: Sort) -> Option<Function> {
    match sort {
        Sort::Bitstring => IS_INDEPENDANT_BITSTRING.const_clone(),
        // Sort::Bool => IS_INDEPENDANT_BOOL.const_clone(),
        _ => None,
    }
}
