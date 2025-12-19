use itertools::{Itertools, chain};

use crate::libraries::AEnc;
use crate::libraries::utils::TwoSortFunction;
use crate::terms::{Formula, Function, NONCE, Rewrite, Sort};
use crate::{Problem, rexp};

pub fn mk_rwrites(pbl: &Problem, aenc: &AEnc) -> impl Iterator<Item = Rewrite> {
    chain![mk_static(pbl, aenc), mk_rewrite_regular(pbl, aenc)]
}

/// Generates rewrite rules for regular functions, introducing PRF candidates.
///
/// This iterates over functions in the problem and creates rewrite rules
/// to propagate `candidate` functions through them.
fn mk_rewrite_regular(pbl: &Problem, aenc: &AEnc) -> impl Iterator<Item = Rewrite> {
    pbl.functions()
        .iter_current()
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| f.is_part_of_F())
        .filter(|f| (!f.is_special_subterm()) || f.is_if_then_else())
        .flat_map(|f| mk_rewrite_one(pbl, aenc, f))
}

/// Creates a single rewrite rule for a given function `f`.
///
/// for `f != hash` this builds for all `n`
/// ```text
/// f(x1,..., xn, candidate(x(n+1), m, k), ...,xm)
///     -> candidate(f(x1,...,xm), m, k)
/// ```
/// effectively lifting the `candidate` function out of the arguments of `f`.
fn mk_rewrite_one(_pbl: &Problem, aenc: &AEnc, f: &Function) -> impl Iterator<Item = Rewrite> {
    let m = crate::fresh!(Bitstring);
    let r = crate::fresh!(Nonce);
    let k = crate::fresh!(Nonce);
    let vars = f.signature.mk_vars();

    let candidate = aenc.candidate.form_sort(f.signature.output).unwrap();
    let ret = rexp!((candidate (f #(vars.iter().map_into())*) #m #r #k));
    let vars_fo = vars.iter().cloned().map(Formula::Var).collect_vec();

    f.signature
        .inputs
        .iter()
        .enumerate()
        .filter_map(move |(i, &s)| {
            let candidate = aenc.candidate.form_sort(s)?;
            let mut args = vars_fo.clone();
            args[i] = rexp!((candidate #(args[i].clone()) #m #r #k));
            Some(
                Rewrite::builder()
                    .prolog_only(true)
                    .variables(chain!([m.clone(), k.clone()], vars.clone()))
                    .from(rexp!((f #args*)))
                    .to(ret.clone())
                    .name(format!("candidate {} {f} arg#{i:}", aenc.enc))
                    .build(),
            )
        })
}

fn mk_static(_pbl: &Problem, aenc: &AEnc) -> impl Iterator<Item = Rewrite> {
    let AEnc {
        enc,
        pk,
        candidate: TwoSortFunction { m: candidate_m, .. },
        ..
    } = aenc;

    if let Some(pk) = pk {
        [
            mk_rewrite!(crate prolog format!(""); (m Bitstring, r Nonce, k Nonce):
          (enc #m (NONCE #r) (pk (NONCE #k)))
            => (candidate_m (enc #m (NONCE #r) (pk (NONCE #k))) #m #r #k)),
        ]
    } else {
        [
            mk_rewrite!(crate prolog format!(""); (m Bitstring, r Nonce, k Nonce):
          (enc #m (NONCE #r) (NONCE #k))
            => (candidate_m (enc #m (NONCE #r) (NONCE #k)) #m #r #k)),
        ]
    }
    .into_iter()
}
