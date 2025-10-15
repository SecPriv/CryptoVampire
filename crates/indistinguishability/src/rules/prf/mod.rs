use std::borrow::Cow;

use egg::{Id, Language, Pattern, Searcher, Var};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain};
use utils::ereturn_let;

use crate::problem::{PAnalysis, PRule};
use crate::terms::{
    EQUIV, Function, FunctionFlags, NONCE, RecFOFormula, SUBSTITUTION, SUBSTITUTION_RULE, Sort,
};
use crate::{Lang, Problem, mk_signature, rexp};

#[cfg(test)]
pub mod test;

mod candidate;
mod search;

#[derive(Debug)]
pub struct PRF {
    hash: Function,
    candidate_bitstring: Function,
    candidate_bool: Function,
    search_bitstring: Function,
    search_bool: Function,
    search_trigger: Function,
    index: usize,
}

macro_rules! declare {
    ($pbl:ident @ $pos:ident: $name:literal; $($s:expr),*) => {
        $pbl
            .declare_function()
            .fresh_name($name)
            .inputs({
                use Sort::*;
                [$($s),*]
            })
            .output(Sort::Bool)
            .flags(FunctionFlags::PROLOG_ONLY)
            .cryptography([$pos])
            .call()
    };
}

declare_trace!($"prf");

impl PRF {
    pub fn new_and_add(pbl: &mut Problem, pos: usize, hash: Function) -> &Self {
        assert_eq!(
            hash.signature,
            mk_signature!((Bitstring, Bitstring) -> Bitstring)
        );
        assert!(hash.cryptography.contains(&pos));

        // h(m, k), m, k
        let candidate_bitstring =
            declare!(pbl@pos: "prf_candidate_bitstring"; Bitstring, Bitstring, Nonce);
        let candidate_bool = declare!(pbl@pos: "prf_candidate_bool"; Bool, Bitstring, Nonce);

        //  m, k ||> x
        let search_bitstring =
            declare!(pbl@pos: "prf_search_bitstring"; Bitstring, Nonce, Bitstring);
        let search_bool = declare!(pbl@pos: "prf_search_bool"; Bitstring, Nonce, Bool);

        // m, k, ptcl, t
        let search_trigger =
            declare!(pbl@pos: "prf_search_trigger"; Bitstring, Nonce, Protocol, Time);

        let prf = Self {
            hash,
            candidate_bitstring,
            candidate_bool,
            search_bitstring,
            search_bool,
            search_trigger,
            index: pos,
        };

        {
            // rules
            let rules = chain![
                prf.mk_prf_rule().map(|x| x.into_mrc()),
                search::mk_rules(pbl, &prf)
            ]
            .collect_vec();
            pbl.extra_rules_mut().extend(rules);
        }

        {
            // rewrites
            let rewrites = chain![candidate::mk_rewrites(pbl, &prf),].collect_vec();
            pbl.extra_rewrite_mut().extend(rewrites);
        }

        let crypt_assumpt = pbl.cryptography_mut(pos).unwrap();
        assert!(crypt_assumpt.is_undefined());
        *crypt_assumpt = prf.into();
        crypt_assumpt.as_prf().unwrap()
    }

    pub fn get_candidate(&self, sort: Sort) -> Option<&Function> {
        match sort {
            Sort::Bitstring => Some(&self.candidate_bitstring),
            Sort::Bool => Some(&self.candidate_bool),
            _ => None,
        }
    }

    pub fn get_search(&self, sort: Sort) -> Option<&Function> {
        match sort {
            Sort::Bitstring => Some(&self.search_bitstring),
            Sort::Bool => Some(&self.search_bool),
            _ => None,
        }
    }

    fn mk_prf_rule(&self) -> [TopPrfRule; 2] {
        let Self {
            hash,
            candidate_bitstring,
            search_bitstring,
            ..
        } = self;
        decl_vars!(u, v, hm:Bitstring, m:Bitstring, k:Nonce, nk:Nonce, b);

        let conclusionl = rexp!((EQUIV #u #v (candidate_bitstring #hm #m #k) #b));
        let conclusionr = rexp!((EQUIV #u #v #b (candidate_bitstring #hm #m #k)));
        let subterm_search1 = rexp!((search_bitstring #m #k #hm));
        let subterm_search2 = rexp!((search_bitstring #m #k #m));
        let new_goall = rexp!((SUBSTITUTION_RULE (EQUIV #u #v (SUBSTITUTION #hm (hash #m (NONCE #k)) (NONCE #nk)) #b)));
        let new_goalr = rexp!((SUBSTITUTION_RULE (EQUIV #u #v #b (SUBSTITUTION #hm (hash #m (NONCE #k)) (NONCE #nk)))));

        [
            TopPrfRule::new(
                &conclusionl,
                &subterm_search1,
                &subterm_search2,
                &new_goall,
                PrfKind::Left,
                candidate_bitstring.clone(),
            ),
            TopPrfRule::new(
                &conclusionr,
                &subterm_search1,
                &subterm_search2,
                &new_goalr,
                PrfKind::Right,
                candidate_bitstring.clone(),
            ),
        ]
    }

    pub fn index(&self) -> usize {
        self.index
    }
}

/// Ochestrating [Rule] for PRF
///
/// This triggers the procedure and will in turn call many other rules
#[derive(Debug, Clone)]
struct TopPrfRule {
    conclusion: Pattern<Lang>,
    subterm_search1: Pattern<Lang>,
    subterm_search2: Pattern<Lang>,
    new_goal: Pattern<Lang>,

    // for debuging
    kind: PrfKind,
    #[allow(dead_code)]
    candidate_bitstring: Function,
}

#[derive(Debug, Clone, Copy)]
enum PrfKind {
    Left,
    Right,
}

impl TopPrfRule {
    fn new(
        conclusion: &RecFOFormula,
        subterm_search1: &RecFOFormula,
        subterm_search2: &RecFOFormula,
        new_goal: &RecFOFormula,
        kind: PrfKind,
        candidate_bitstring: Function,
    ) -> Self {
        Self {
            conclusion: conclusion.into(),
            subterm_search1: subterm_search1.into(),
            subterm_search2: subterm_search2.into(),
            new_goal: new_goal.into(),
            kind,
            candidate_bitstring,
        }
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>> for TopPrfRule {
    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: Id) -> Dependancy {
        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs)= self.conclusion.search_eclass(egraph, goal), Dependancy::impossible());

        if cfg!(debug_assertions) {
            check_hash_eq_nonce(egraph);
        }

        let n = {
            let pblm = egraph.analysis.pbl_mut();

            let fun = pblm
                .declare_function()
                .fresh_name("n_prf")
                .flags(FunctionFlags::NONCE)
                .output(Sort::Nonce)
                .call();

            egraph.add(fun.app_id([]))
        };
        substs
            .substs
            .into_iter()
            .map(|mut subst| {
                subst.insert(Var::from_usize(7), n);

                [
                    self.subterm_search1.apply_susbt(egraph, &subst),
                    self.subterm_search2.apply_susbt(egraph, &subst),
                    self.new_goal.apply_susbt(egraph, &subst),
                ]
            })
            .collect()
    }

    fn name(&self) -> std::borrow::Cow<'_, str> {
        match self.kind {
            PrfKind::Left => Cow::Borrowed("prf left"),
            PrfKind::Right => Cow::Borrowed("prf right"),
        }
    }
}

fn check_hash_eq_nonce<'a>(egraph: &mut egg::EGraph<Lang, PAnalysis<'a>>) {
    let pblm = egraph.analysis.pbl();
    let hash_funs = pblm
        .cryptography()
        .iter()
        .filter_map(|c| match c {
            crate::terms::CryptographicAssumption::PRF(prf) => Some(prf.hash.clone()),
            _ => None,
        })
        .collect_vec();

    let mut to_explain = Vec::new();

    for eclass in egraph.classes() {
        let hashes = eclass
            .nodes
            .iter()
            .find(|f| hash_funs.contains(&f.discriminant()));
        let nonces = eclass.nodes.iter().find(|f| f.discriminant() == NONCE);

        if let Some(h) = hashes
            && let Some(nonce) = nonces
        {
            let h = h.discriminant().app(
                &h.children()
                    .iter()
                    .map(|&c| egraph.id_to_expr(c))
                    .collect_vec(),
            );
            let n = nonce.discriminant().app(
                &nonce
                    .children()
                    .iter()
                    .map(|&c| egraph.id_to_expr(c))
                    .collect_vec(),
            );
            to_explain.push((h, n, eclass.id));
        }
    }

    for (h, n, _) in &to_explain {
        let mut e = egraph.explain_equivalence(h, n);
        eprintln!("impossible equivalence:\n{}", e.get_flat_string());
    }
    if let Some((_, _, id)) = to_explain.pop() {
        panic!("shared nonce and hash in {:}", egraph.id_to_expr(id))
    }
}
