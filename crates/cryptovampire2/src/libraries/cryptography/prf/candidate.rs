use itertools::{Itertools, chain};
use utils::{econtinue_if, econtinue_let};

use crate::libraries::PRF;
use crate::libraries::utils::RewriteSink;
use crate::terms::{Formula, Function, NONCE, Rewrite, Sort};
use crate::{Problem, fresh, rexp};

/// Generates rewrite rules for PRF candidates.
///
/// These rules are used to introduce `candidate` functions into the e-graph,
/// which are essential for reasoning about PRF indistinguishability.
pub fn add_rewrites(pbl: &Problem, prf: &PRF, sink: &mut impl RewriteSink) {
    sink.add_rewrite(pbl, mk_rewrite_init(pbl, prf));
    add_rewrite_regular(pbl, prf, sink);
}

/// Creates an initial rewrite rule for PRF candidates.
///
/// for `f != hash` this builds for all `n`
/// ```text
/// h(m, nonce(k))
///     -> candidate(h(m, nonce(k)), m, k)
/// ```
fn mk_rewrite_init(
    _pbl: &Problem,
    PRF {
        hash,
        candidate_bitstring: candidate,
        ..
    }: &PRF,
) -> Rewrite {
    decl_vars!(m:Bitstring, k:Nonce);
    Rewrite::builder()
        .prolog_only(true)
        .from(rexp!((hash #m (NONCE #k))))
        .to(rexp!((candidate (hash #m (NONCE #k)) #m #k)))
        .variables([m, k].map(Clone::clone))
        .name(format!("candidate prf success ({hash})"))
        .build()
}

/// Generates rewrite rules for regular functions, introducing PRF candidates.
///
/// This iterates over functions in the problem and creates rewrite rules
/// to propagate `candidate` functions through them.
fn add_rewrite_regular(pbl: &Problem, prf: &PRF, sink: &mut impl RewriteSink) {
    for f in pbl.functions().iter_current() {
        econtinue_if!(f.is_out_of_term_algebra());
        econtinue_if!(!matches!(f.signature.output, Sort::Bitstring | Sort::Bool));
        econtinue_if!(f.is_special_subterm() && !f.is_if_then_else());
        add_rewrite_one(pbl, prf, f, sink);
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
fn add_rewrite_one(pbl: &Problem, prf: &PRF, f: &Function, sink: &mut impl RewriteSink) {
    let m = fresh!(Bitstring);
    let k = fresh!(Nonce);
    let vars = f.signature.mk_vars();

    let candidate = prf.get_candidate(f.signature.output).unwrap();
    let ret = rexp!((candidate (f #(vars.iter().map_into())*) #m #k));
    let vars_fo = vars.iter().cloned().map(Formula::Var).collect_vec();

    sink.reserve(f.arity());
    for (i, s) in f.signature.inputs.iter().enumerate() {
        econtinue_let!(let Some(candidate) = prf.get_candidate(*s));
        let mut args = vars_fo.clone();
        args[i] = rexp!((candidate #(args[i].clone()) #m #k));
        sink.add_rewrite(
            pbl,
            Rewrite::builder()
                .prolog_only(true)
                .variables(chain!([m.clone(), k.clone()], vars.clone()))
                .from(rexp!((f #args*)))
                .to(ret.clone())
                .name(format!("candidate prf#{:} {f} arg#{i:}", prf.index()))
                .build(),
        );
    }
}
