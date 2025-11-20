use itertools::{Itertools, chain};

use crate::libraries::DDH;
use crate::terms::{Formula, Function, NONCE, Rewrite, Sort};
use crate::{Problem, rexp};
// super::vars::*;

pub fn mk_rwrites(pbl: &Problem, ddh: &DDH) -> impl Iterator<Item = Rewrite> {
    chain![mk_static(pbl, ddh), mk_rewrite_regular(pbl, ddh)]
}

/// Generates rewrite rules for regular functions, introducing PRF candidates.
///
/// This iterates over functions in the problem and creates rewrite rules
/// to propagate `candidate` functions through them.
fn mk_rewrite_regular(pbl: &Problem, ddh: &DDH) -> impl Iterator<Item = Rewrite> {
    pbl.functions()
        .iter_current()
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| f.is_part_of_F())
        .filter(|f| (!f.is_special_subterm()) || f.is_if_then_else())
        .flat_map(|f| mk_rewrite_one(pbl, ddh, f))
}

/// Creates a single rewrite rule for a given function `f`.
///
/// ```text
/// f(x1,..., xn, candidate(x(n+1), m, k), ...,xm)
///     -> candidate(f(x1,...,xm), m, k)
/// ```
/// effectively lifting the `candidate` function out of the arguments of `f`.
fn mk_rewrite_one(_pbl: &Problem, aenc: &DDH, f: &Function) -> impl Iterator<Item = Rewrite> {
    let na = crate::fresh!(Nonce);
    let nb = crate::fresh!(Nonce);
    let vars = f.signature.mk_vars();

    let candidate = aenc.get_candidate(f.signature.output).unwrap();
    let ret = rexp!((candidate (f #(vars.iter().map_into())*) #na #nb));
    let vars_fo = vars.iter().cloned().map(Formula::Var).collect_vec();

    f.signature
        .inputs
        .iter()
        .enumerate()
        .filter_map(move |(i, &s)| {
            let candidate = aenc.get_candidate(s)?;
            let mut args = vars_fo.clone();
            args[i] = rexp!((candidate #(args[i].clone()) #na #nb));
            Some(
                Rewrite::builder()
                    .prolog_only(true)
                    .variables(chain!([&na, &nb]).cloned())
                    .from(rexp!((f #args*)))
                    .to(ret.clone())
                    .name(format!("candidate ddh {} {f} arg#{i:}", aenc.exp))
                    .build(),
            )
        })
}

fn mk_static(_pbl: &Problem, ddh: &DDH) -> impl Iterator<Item = Rewrite> {
    let DDH {
        candidate_m,
        g,
        exp,
        ..
    } = ddh;
    [
        mk_rewrite!(crate prolog format!(""); (a Bitstring, b Nonce):
          (exp (exp g (NONCE #a)) (NONCE #b))
            => (candidate_m (exp (exp g (NONCE #a)) (NONCE #b)) #a #b)),
    ]
    .into_iter()
}
