use itertools::{Itertools, chain};
use utils::{econtinue_if, econtinue_let};

use crate::libraries::AEnc;
use crate::libraries::utils::{RewriteSink, RuleSink, TwoSortFunction};
use crate::terms::{Formula, Function, NONCE, Rewrite, Sort};
use crate::{Problem, rexp};

pub fn add_rwrites(pbl: &Problem, aenc: &AEnc, sink: &mut impl RewriteSink) {
    add_static(pbl, aenc, sink);
    add_rewrite_regular(pbl, aenc, sink);
}

/// Generates rewrite rules for regular functions, introducing PRF candidates.
///
/// This iterates over functions in the problem and creates rewrite rules
/// to propagate `candidate` functions through them.
fn add_rewrite_regular(pbl: &Problem, aenc: &AEnc, sink: &mut impl RewriteSink) {
    for f in pbl.functions().iter_current() {
        econtinue_if!(!matches!(f.signature.output, Sort::Bitstring | Sort::Bool));
        econtinue_if!(!f.is_part_of_F());
        econtinue_if!(f.is_special_subterm() && !f.is_if_then_else());
        add_rewrite_one(pbl, aenc, f, sink);
    }
}

/// Creates a single rewrite rule for a given function `f`.
///
/// for `f != hash` this builds for all `n`
/// ```text
/// f(x1,..., xn, candidate(x(n+1), m, k), ...,xm)
///     -> candidate(f(x1,...,xm), m, k)
/// ```
/// effectively lifting the `candidate` function out of the arguments of `f`.
fn add_rewrite_one(pbl: &Problem, aenc: &AEnc, f: &Function, sink: &mut impl RewriteSink) {
    let m = crate::fresh!(Bitstring);
    let r = crate::fresh!(Nonce);
    let k = crate::fresh!(Nonce);
    let vars = f.signature.mk_vars();

    let candidate = aenc.candidate.from_sort(f.signature.output).unwrap();
    let ret = rexp!((candidate (f #(vars.iter().map_into())*) #m #r #k));
    let vars_fo = vars.iter().cloned().map(Formula::Var).collect_vec();
    let _ = candidate;

    sink.reserve(f.arity()); // <- a bit too much, but should be almost tight almost all the time
    for (i, s) in f.args_sorts().enumerate() {
        econtinue_let!(let Some(candidate) = aenc.candidate.from_sort(s));
        let mut args = vars_fo.clone();
        args[i] = rexp!((candidate #(args[i].clone()) #m #r #k));
        sink.add_rewrite(
            pbl,
            Rewrite::builder()
                .prolog_only(true)
                .variables(chain!([m.clone(), k.clone()], vars.clone()))
                .from(rexp!((f #args*)))
                .to(ret.clone())
                .name(format!("candidate {} {f} arg#{i:}", aenc.enc))
                .build(),
        );
    }
}

fn add_static(pbl: &Problem, aenc: &AEnc, sink: &mut impl RewriteSink) {
    let AEnc {
        enc,
        pk,
        candidate: TwoSortFunction { m: candidate_m, .. },
        ..
    } = aenc;

    if let Some(pk) = pk {
        sink.add_rewrite(pbl,
            mk_rewrite!(crate prolog format!("enc candidate trigger"); (m Bitstring, r Nonce, k Nonce):
          (enc #m (NONCE #r) (pk (NONCE #k)))
            => (candidate_m (enc #m (NONCE #r) (pk (NONCE #k))) #m #r #k))
        )
    } else {
        sink.add_rewrite(pbl,
            mk_rewrite!(crate prolog format!("enc candidate trigger"); (m Bitstring, r Nonce, k Nonce):
          (enc #m (NONCE #r) (NONCE #k))
            => (candidate_m (enc #m (NONCE #r) (NONCE #k)) #m #r #k)))
    }
}
