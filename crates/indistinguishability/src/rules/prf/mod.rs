use std::borrow::Cow;

use egg::{Analysis, EGraph, Id, Language, Pattern, Searcher, Subst};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain};
use rustc_hash::FxHashSet;
use static_init::dynamic;
use utils::{ebreak_if, ebreak_let, ereturn_let, implvec};

use crate::problem::{PAnalysis, PRule};
use crate::terms::utils::iter_egraph::iter_descendants_lang;
use crate::terms::{
    EQUIV, FRESH_NONCE, Function, FunctionFlags, NONCE, RecFOFormula,
    SUBSTITUTION, SUBSTITUTION_RULE, Sort, TRUE,
};
use crate::{Lang, Problem, mk_signature, rexp};

#[cfg(test)]
pub mod test;

mod candidate;
mod search;

/// Represents a Pseudo-Random Function (PRF) and associated functions for its analysis.
#[derive(Debug)]
pub struct PRF {
    /// The hash function associated with this PRF.
    hash: Function,
    /// Candidate function for bitstring outputs.
    candidate_bitstring: Function,
    /// Candidate function for boolean outputs.
    candidate_bool: Function,
    /// Search function for bitstring outputs.
    search_bitstring: Function,
    /// Search function for boolean outputs.
    search_bool: Function,
    /// Trigger function for PRF searches.
    search_trigger: Function,
    /// The index of this PRF in the problem's cryptographic assumptions.
    index: usize,
}

macro_rules! declare {
    ($pbl:ident @ $pos:ident: $name:literal; $($s:expr),* => $o:ident) => {
        $pbl
            .declare_function()
            .fresh_name($name)
            .inputs({
                use Sort::*;
                [$($s),*]
            })
            .output(Sort::$o)
            .flags(FunctionFlags::PROLOG_ONLY)
            .cryptography([$pos])
            .call()
    };
}

declare_trace!($"prf");

impl PRF {
    /// Creates a new `PRF` instance and adds its associated functions and rules to the problem.
    ///
    /// # Arguments
    ///
    /// * `pbl` - A mutable reference to the `Problem`.
    /// * `pos` - The position/index of this PRF in the problem's cryptographic assumptions.
    /// * `hash` - The hash function to be used as the PRF.
    ///
    /// # Panics
    ///
    /// Panics if the `hash` function's signature is not `(Bitstring, Bitstring) -> Bitstring`,
    /// or if the `hash` function does not contain `pos` in its cryptography, or if the
    /// cryptographic assumption at `pos` is already defined.
    pub fn new_and_add(pbl: &mut Problem, pos: usize, hash: Function) -> &Self {
        tr!("{}", hash.name);
        assert_eq!(
            hash.signature,
            mk_signature!((Bitstring, Bitstring) -> Bitstring)
        );
        assert!(hash.cryptography.contains(&pos));

        // h(m, k), m, k
        let candidate_bitstring =
            declare!(pbl@pos: "prf_candidate_bitstring"; Bitstring, Bitstring, Nonce => Bitstring);
        let candidate_bool =
            declare!(pbl@pos: "prf_candidate_bool"; Bool, Bitstring, Nonce => Bool);

        //  m, k ||> x | h
        let search_bitstring =
            declare!(pbl@pos: "prf_search_bitstring"; Bitstring, Nonce, Bitstring, Bool => Bool);
        let search_bool =
            declare!(pbl@pos: "prf_search_bool"; Bitstring, Nonce, Bool, Bool => Bool);

        // m, k, ptcl, t, h
        let search_trigger =
            declare!(pbl@pos: "prf_search_trigger"; Bitstring, Nonce, Protocol, Time, Bool => Bool);

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

    /// Returns the candidate function for a given output sort.
    pub fn get_candidate(&self, sort: Sort) -> Option<&Function> {
        match sort {
            Sort::Bitstring => Some(&self.candidate_bitstring),
            Sort::Bool => Some(&self.candidate_bool),
            _ => None,
        }
    }

    /// Returns the search function for a given output sort.
    pub fn get_search(&self, sort: Sort) -> Option<&Function> {
        match sort {
            Sort::Bitstring => Some(&self.search_bitstring),
            Sort::Bool => Some(&self.search_bool),
            _ => None,
        }
    }

    /// Creates the two main PRF rules (left and right) for the e-graph.
    fn mk_prf_rule(&self) -> [TopPrfRule; 2] {
        let Self {
            hash,
            candidate_bitstring,
            search_bitstring,
            ..
        } = self;

        let conclusionl = rexp!((EQUIV #U #V (candidate_bitstring #HM #M #K) #B));
        let conclusionr = rexp!((EQUIV #U #V #B (candidate_bitstring #HM #M #K)));
        let subterm_hm = rexp!((search_bitstring #M #K #HM true));
        let subterm_m = rexp!((search_bitstring #M #K #M true));
        let freshl = rexp!((FRESH_NONCE #NK #U true));
        let freshr = rexp!((FRESH_NONCE #NK #V true));
        let new_goall = rexp!((SUBSTITUTION_RULE (EQUIV #U #V (SUBSTITUTION #HM (hash #M (NONCE #K)) (NONCE #NK)) #B)));
        let new_goalr = rexp!((SUBSTITUTION_RULE (EQUIV #U #V #B (SUBSTITUTION #HM (hash #M (NONCE #K)) (NONCE #NK)))));

        [
            TopPrfRule::new(
                &conclusionl,
                &subterm_hm,
                &subterm_m,
                &freshl,
                &new_goall,
                PrfKind::Left,
                candidate_bitstring.clone(),
            ),
            TopPrfRule::new(
                &conclusionr,
                &subterm_hm,
                &subterm_m,
                &freshr,
                &new_goalr,
                PrfKind::Right,
                candidate_bitstring.clone(),
            ),
        ]
    }

    /// Returns the index of this PRF in the problem's cryptographic assumptions.
    pub fn index(&self) -> usize {
        self.index
    }
}

#[dynamic]
static PATTERN_FRESH_SEARCH_INNER: Pattern<Lang> =
    Pattern::from(&rexp!((FRESH_NONCE #NK #HM true)));

decl_vars!(const; U, V, HM:Bitstring, M:Bitstring, K:Nonce, NK:Nonce, B);

/// Ochestrating [Rule] for PRF
///
/// This triggers the procedure and will in turn call many other rules
#[derive(Debug, Clone)]
struct TopPrfRule {
    /// The conclusion pattern to search for in the e-graph.
    conclusion: Pattern<Lang>,
    /// The  subterm search hm.
    subterm_hm: Pattern<Lang>,
    /// The  subterm search m.
    subterm_m: Pattern<Lang>,
    /// The subterm search fresh u/v.
    subterm_hyp: Pattern<Lang>,
    /// The new goal pattern to apply after a match.
    new_goal: Pattern<Lang>,

    // for debuging
    /// The kind of PRF rule (Left or Right).
    kind: PrfKind,
    #[allow(dead_code)]
    /// The candidate bitstring function associated with this rule.
    candidate_bitstring: Function,
}

/// Specifies the kind of PRF rule, either Left or Right.
#[derive(Debug, Clone, Copy)]
enum PrfKind {
    /// Represents the left-hand side PRF rule.
    Left,
    /// Represents the right-hand side PRF rule.
    Right,
}

impl TopPrfRule {
    /// Creates a new `TopPrfRule`.
    fn new(
        conclusion: &RecFOFormula,
        subterm_hm: &RecFOFormula,
        subterm_m: &RecFOFormula,
        subterm_hyp: &RecFOFormula,
        new_goal: &RecFOFormula,
        kind: PrfKind,
        candidate_bitstring: Function,
    ) -> Self {
        Self {
            conclusion: conclusion.into(),
            subterm_hm: subterm_hm.into(),
            subterm_m: subterm_m.into(),
            subterm_hyp: subterm_hyp.into(),
            new_goal: new_goal.into(),
            kind,
            candidate_bitstring,
        }
    }

    fn generate_fresh_nonce<'a>(
        &self,
        egraph: &mut EGraph<Lang, PAnalysis<'a>>,
        substs: &[Subst],
    ) -> Vec<Id> {
        // try to look for
        'a: {
            let nonces = get_prf(egraph);
            ebreak_if!('a, nonces.is_empty());

            let [hyp, c, other_hyp, other_b] = match self.kind {
                PrfKind::Left => [U, HM, V, B],
                PrfKind::Right => [V, HM, U, B],
            };

            let other_ids = substs
                .iter()
                .cartesian_product([other_hyp, other_b])
                .map(|(s, v)| s.get(v.as_egg()).unwrap())
                .copied();
            let self_ids = substs
                .iter()
                .cartesian_product([hyp, c])
                .map(|(s, v)| s.get(v.as_egg()).unwrap())
                .copied();
            let nonces: FxHashSet<_> = nonces
                .difference(&all_nonce_descendants(egraph, self_ids))
                .copied()
                .collect();
            ebreak_if!('a, nonces.is_empty());

            let all_other = all_nonce_descendants(egraph, other_ids);

            let with_other = nonces.intersection(&all_other).copied().collect_vec();
            ebreak_if!('a, with_other.is_empty());

            let mut without_other = nonces.difference(&all_other).copied();
            ebreak_let!('a, let Some(without_other)= without_other.next());

            return chain![with_other, [without_other]].collect();
        }

        // else generate new nonce
        if egraph.analysis.pbl().state.n_prf.len() <= egraph.analysis.pbl().config.prf_limit {
            let fun = egraph
                .analysis
                .pbl_mut()
                .declare_function()
                .fresh_name("n_prf")
                .flags(FunctionFlags::NONCE)
                .output(Sort::Nonce)
                .call();
            let n = egraph.add(fun.app_id([]));
            let etrue = egraph.add(TRUE.app_id([]));

            let mut msubst = Subst::with_capacity(2);
            msubst.insert(NK.as_egg(), n);

            // make `(fresh_nonce n _ true)` hold for a bunch of them
            for g in [U, V, B, HM] {
                for subst in substs.iter() {
                    msubst.insert(HM.as_egg(), *subst.get(g.as_egg()).unwrap());
                    let fresh = PATTERN_FRESH_SEARCH_INNER.apply_susbt(egraph, &msubst);
                    egraph.union(etrue, fresh);
                }
            }

            get_prf_mut(egraph).insert(n);
        }

        get_prf(egraph).iter().cloned().collect()
    }
}

fn get_prf<'a, 'b>(egraph: &'b EGraph<Lang, PAnalysis<'a>>) -> &'b FxHashSet<Id> {
    &egraph.analysis.pbl().state.n_prf
}

fn get_prf_mut<'a, 'b>(egraph: &'b mut EGraph<Lang, PAnalysis<'a>>) -> &'b mut FxHashSet<Id> {
    &mut egraph.analysis.pbl_mut().state.n_prf
}

impl PrfKind {
    pub const fn other(self) -> Self {
        match self {
            Self::Left => Self::Right,
            Self::Right => Self::Left,
        }
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>> for TopPrfRule {
    /// Searches for the conclusion pattern in the e-graph and applies the PRF rule.
    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: Id) -> Dependancy {
        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs)= self.conclusion.search_eclass(egraph, goal), Dependancy::impossible());

        if cfg!(debug_assertions) {
            check_hash_eq_nonce(egraph);
        }

        let nonces = self.generate_fresh_nonce(egraph, &substs.substs);

        let mut res = Vec::with_capacity(nonces.len() * substs.substs.len());
        for n in nonces {
            for subst in &substs.substs {
                let mut subst = subst.clone();
                subst.insert(NK.as_egg(), n);

                let r = [
                    PATTERN_FRESH_SEARCH_INNER.apply_susbt(egraph, &subst),
                    self.subterm_hyp.apply_susbt(egraph, &subst),
                    self.subterm_hm.apply_susbt(egraph, &subst),
                    self.subterm_m.apply_susbt(egraph, &subst),
                    self.new_goal.apply_susbt(egraph, &subst),
                ];
                res.push(r);
            }
        }
        res.into_iter().collect()
    }

    /// Returns the name of this rule, based on its `PrfKind`.
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

fn all_nonce_descendants<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    ancestors: implvec!(Id),
) -> FxHashSet<Id> {
    iter_descendants_lang(egraph, ancestors, can_have_children)
        .filter(|&x| (x.head == NONCE))
        .map(|x| x.args[0])
        .collect()
}

fn can_have_children(f: &Function) -> bool {
    f.is_egg_binder() || (f.is_part_of_F() && !f.is_alias())
}
