use itertools::{Itertools, chain};

use crate::libraries::PRF;
use crate::terms::{Formula, Function, NONCE, Rewrite, Sort};
use crate::{Problem, fresh, rexp};

/// Generates an iterator of rewrite rules for PRF candidates.
///
/// These rules are used to introduce `candidate` functions into the e-graph,
/// which are essential for reasoning about PRF indistinguishability.
pub fn mk_rewrites<'a>(pbl: &'a Problem, prf: &'a PRF) -> impl Iterator<Item = Rewrite> + use<'a> {
    chain![[mk_rewrite_init(pbl, prf)], mk_rewrite_regular(pbl, prf)]
}

/// Creates an initial rewrite rule for PRF candidates.
///
/// for `f != hash` this builds for all `n`
/// ```text
/// h(m, nonce(k))
///     -> candidate(h(m, nonce(k)), m, k)
/// ```
fn mk_rewrite_init<'a>(
    _pbl: &'a Problem,
    PRF {
        hash,
        candidate_bitstring: candidate,
        ..
    }: &'a PRF,
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
fn mk_rewrite_regular<'a>(pbl: &'a Problem, prf: &'a PRF) -> impl Iterator<Item = Rewrite> {
    pbl.functions()
        .iter_current()
        .filter(|f| !f.is_out_of_term_algebra())
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| (!f.is_special_subterm()) || f.is_if_then_else())
        .flat_map(|f| mk_rewrite_one(pbl, prf, f))
}

/// Creates a single rewrite rule for a given function `f`.
///
/// for `f != hash` this builds for all `n`
/// ```text
/// f(x1,..., xn, candidate(x(n+1), m, k), ...,xm)
///     -> candidate(f(x1,...,xm), m, k)
/// ```
/// effectively lifting the `candidate` function out of the arguments of `f`.
fn mk_rewrite_one<'a>(
    _pbl: &'a Problem,
    prf: &'a PRF,
    f: &'a Function,
) -> impl Iterator<Item = Rewrite> + use<'a> {
    let m = fresh!(Bitstring);
    let k = fresh!(Nonce);
    let vars = f.signature.mk_vars();

    let candidate = prf.get_candidate(f.signature.output).unwrap();
    let ret = rexp!((candidate (f #(vars.iter().map_into())*) #m #k));
    let vars_fo = vars.iter().cloned().map(Formula::Var).collect_vec();

    f.signature
        .inputs
        .iter()
        .enumerate()
        .filter_map(move |(i, &s)| {
            let candidate = prf.get_candidate(s)?;
            let mut args = vars_fo.clone();
            args[i] = rexp!((candidate #(args[i].clone()) #m #k));
            Some(
                Rewrite::builder()
                    .prolog_only(true)
                    .variables(chain!([m.clone(), k.clone()], vars.clone()))
                    .from(rexp!((f #args*)))
                    .to(ret.clone())
                    .name(format!("candidate prf {f} arg#{i:}"))
                    .build(),
            )
        })
}
