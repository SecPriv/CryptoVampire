use itertools::{Itertools, chain};
use utils::{econtinue_if, econtinue_let};

use crate::libraries::DDH;
use crate::libraries::utils::RewriteSink;
use crate::terms::{Formula, Function, NONCE, Rewrite, Sort};
use crate::{Problem, rexp};
// super::vars::*;

pub fn add_rwrites(pbl: &Problem, ddh: &DDH, sink: &mut impl RewriteSink) {
    add_static(pbl, ddh, sink);
    add_rewrite_regular(pbl, ddh, sink);
}

/// Generates rewrite rules for regular functions, introducing PRF candidates.
///
/// This iterates over functions in the problem and creates rewrite rules
/// to propagate `candidate` functions through them.
fn add_rewrite_regular(pbl: &Problem, ddh: &DDH, sink: &mut impl RewriteSink) {
    for f in pbl.functions().iter_current() {
        econtinue_if!(!matches!(f.signature.output, Sort::Bitstring | Sort::Bool));
        econtinue_if!(!f.is_part_of_F());
        econtinue_if!(f.is_special_subterm() && !f.is_if_then_else());
        add_rewrite_one(pbl, ddh, f, sink);
    }
}

/// Creates a single rewrite rule for a given function `f`.
///
/// ```text
/// f(x1,..., xn, candidate(x(n+1), m, k), ...,xm)
///     -> candidate(f(x1,...,xm), m, k)
/// ```
/// effectively lifting the `candidate` function out of the arguments of `f`.
fn add_rewrite_one(pbl: &Problem, aenc: &DDH, f: &Function, sink: &mut impl RewriteSink) {
    let na = crate::fresh!(Nonce);
    let nb = crate::fresh!(Nonce);
    let vars = f.signature.mk_vars();

    let candidate = aenc.get_candidate(f.signature.output).unwrap();
    let ret = rexp!((candidate (f #(vars.iter().map_into())*) #na #nb));
    let vars_fo = vars.iter().cloned().map(Formula::Var).collect_vec();

    sink.reserve(f.arity());
    for (i, s) in f.signature.inputs.iter().enumerate() {
        econtinue_let!(let Some(candidate) = aenc.get_candidate(*s));
        let mut args = vars_fo.clone();
        args[i] = rexp!((candidate #(args[i].clone()) #na #nb));
        sink.add_rewrite(
            pbl,
            Rewrite::builder()
                .prolog_only(true)
                .variables(chain!([&na, &nb]).cloned())
                .from(rexp!((f #args*)))
                .to(ret.clone())
                .name(format!("candidate ddh {} {f} arg#{i:}", aenc.exp))
                .build(),
        );
    }
}

fn add_static(pbl: &Problem, ddh: &DDH, sink: &mut impl RewriteSink) {
    let DDH {
        candidate_m,
        g,
        exp,
        ..
    } = ddh;
    sink.add_rewrite(
        pbl,
        mk_rewrite!(crate prolog format!("ddh candidate trigger"); (a Nonce, b Nonce):
          (exp (exp g (NONCE #a)) (NONCE #b))
            => (candidate_m (exp (exp g (NONCE #a)) (NONCE #b)) #a #b)),
    )
}
