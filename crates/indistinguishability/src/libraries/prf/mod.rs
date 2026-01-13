use std::borrow::Cow;

use egg::{Id, Language, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain};
use static_init::dynamic;
use utils::ereturn_let;

use crate::libraries::utils::RuleWithFreshNonce;
use crate::problem::{PAnalysis, PRule, ProblemState, RcRule};
use crate::terms::{
    CryptographicAssumption, Cryptography, EQUIV, FALSE, FRESH_NONCE, Formula, Function,
    FunctionFlags, NONCE, Sort, TRUE, Variable,
};
use crate::{CVProgram, Lang, Problem, mk_signature, rexp};

declare_trace!($"prf");

#[cfg(test)]
pub mod test;

mod candidate;
mod search;
mod substitute;

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

    subst_left: Function,
    subst_right: Function,

    /// The index of this PRF in the problem's cryptographic assumptions.
    index: usize,
}

#[derive(Debug, Clone)]
enum PRFProof {
    /// keep the element as is
    Keep,
    /// This is an instance of the hash (i.e., replace it with the new nonce)
    Instance,
    /// Apply this function
    ///
    /// Be careful when applying `hash`
    Apply(Function),
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

        //  m, k, nprf ||> x | h
        let search_bitstring = declare!(pbl@pos: "prf_search_bitstring"; Bitstring, Nonce, Nonce, Bitstring, Bool => Bool);
        let search_bool =
            declare!(pbl@pos: "prf_search_bool"; Bitstring, Nonce, Nonce, Bool, Bool => Bool);

        // m, k, ptcl, t, h
        let search_trigger =
            declare!(pbl@pos: "prf_search_trigger"; Bitstring, Nonce, Protocol, Time, Bool => Bool);

        // u, v, m, k, nk, poof, other
        let subst_left = declare!(pbl@pos: "prf_subst_left"; Bitstring, Bitstring, Bitstring, Nonce, Nonce, Bool, Bitstring => Bool);
        // u, v, m, k, nk, proof, other
        let subst_right = declare!(pbl@pos: "prf_subst_right"; Bitstring, Bitstring,  Bitstring, Nonce, Nonce, Bool, Bitstring => Bool);

        let prf = Self {
            hash,
            candidate_bitstring,
            candidate_bool,
            search_bitstring,
            search_bool,
            search_trigger,
            subst_left,
            subst_right,
            index: pos,
        };

        {
            // rules
            let rules = chain![
                prf.mk_prf_rule().map(|x| x.into_mrc()),
                prf.mk_subst_rules().map(|x| x.into_mrc()),
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

        prf.register_at(pbl, pos).unwrap()
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
            candidate_bitstring,
            search_bitstring,
            subst_left,
            subst_right,
            ..
        } = self;

        let conclusionl = rexp!((EQUIV #U #V (candidate_bitstring #HM #M #K) #B));
        let conclusionr = rexp!((EQUIV #U #V #B (candidate_bitstring #HM #M #K)));
        let subterm_hm = rexp!((search_bitstring #M #K #NK #HM true));
        let subterm_m = rexp!((search_bitstring #M #K #NK #M true));
        let freshl = rexp!((FRESH_NONCE #NK #U true));
        let freshr = rexp!((FRESH_NONCE #NK #V true));

        let new_goall =
            rexp!((subst_left #U #V #M #K #NK (search_bitstring #M #K #NK #HM true) #B));
        let new_goalr =
            rexp!((subst_right #U #V #M #K #NK (search_bitstring #M #K #NK #HM true) #B));

        // let new_goall = rexp!((SUBSTITUTION_RULE (EQUIV #U #V (SUBSTITUTION #HM (hash #M (NONCE #K)) (NONCE #NK)) #B)));
        // let new_goalr = rexp!((SUBSTITUTION_RULE (EQUIV #U #V #B (SUBSTITUTION #HM (hash #M (NONCE #K)) (NONCE #NK)))));

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

    fn mk_subst_rules(&self) -> [substitute::SubstRule; 2] {
        let Self {
            subst_left,
            subst_right,
            index,
            ..
        } = self;

        let trigger_l = rexp!((subst_left #U #V #M #K #NK #PROOF #B));
        let trigger_r = rexp!((subst_right #U #V #M #K #NK #PROOF #B));
        let new_goal_l = rexp!((EQUIV #U #V #NEW_TERM #B));
        let new_goal_r = rexp!((EQUIV #U #V #B #NEW_TERM));

        [
            substitute::SubstRule::builder()
                .new_goal(&new_goal_l)
                .trigger(&trigger_l)
                .prf_idx(*index)
                .build(),
            substitute::SubstRule::builder()
                .new_goal(&new_goal_r)
                .trigger(&trigger_r)
                .prf_idx(*index)
                .build(),
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

decl_vars!(const; U, V, HM:Bitstring, M:Bitstring, NEW_TERM: Bitstring,  K:Nonce, NK:Nonce, B, PROOF: Bool);

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
        conclusion: &Formula,
        subterm_hm: &Formula,
        subterm_m: &Formula,
        subterm_hyp: &Formula,
        new_goal: &Formula,
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
}

impl RuleWithFreshNonce for TopPrfRule {
    fn get_set_mut<'a>(&self, pbl: &'a mut Problem) -> &'a mut super::utils::FreshNonceSet {
        &mut pbl.state.n_prf
    }

    fn get_set<'a>(&self, pbl: &'a Problem) -> &'a super::utils::FreshNonceSet {
        &pbl.state.n_prf
    }

    fn get_bound(&self, pbl: &Problem) -> Option<usize> {
        Some(pbl.config.prf_limit)
    }

    fn mk_fresh_function(&self, pbl: &mut Problem) -> Function {
        pbl.declare_function()
            .fresh_name("n_prf")
            .flags(FunctionFlags::NONCE | FunctionFlags::FRESH)
            .output(Sort::Nonce)
            .call()
        // todo!()
    }
}

#[dynamic]
static PATTERN_FALSE: Pattern<Lang> = Pattern::from(&rexp!(false));

impl PrfKind {
    #[allow(dead_code)]
    pub const fn other(self) -> Self {
        match self {
            Self::Left => Self::Right,
            Self::Right => Self::Left,
        }
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for TopPrfRule {
    /// Searches for the conclusion pattern in the e-graph and applies the PRF rule.
    fn search(&self, prgm: &mut CVProgram<'a>, goal: Id) -> Dependancy {
        ereturn_let!(let Some(substs)= self.conclusion.search_eclass(prgm.egraph(), goal), Dependancy::impossible());

        if cfg!(debug_assertions) {
            check_hash_eq_nonce(prgm.egraph_mut());
        }
        let [hyp, c, other_hyp, other_b] = match self.kind {
            PrfKind::Left => [U, HM, V, B],
            PrfKind::Right => [V, HM, U, B],
        };

        let mut res = Vec::new();
        for mut subst in substs.substs {
            let [other_hyp, other_b, hyp, c] =
                [other_hyp, other_b, hyp, c].map(|v| *subst.get(v.as_egg()).unwrap());
            let nonces = self.generate_fresh_nonce(prgm, [hyp, c], [other_hyp, other_b]);

            for n in nonces {
                subst.insert(NK.as_egg(), n);

                let egraph = prgm.egraph_mut();
                let r = [
                    // PATTERN_FRESH_SEARCH_INNER.apply_susbt(egraph, &subst),
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

    if let Some(t) = egraph.lookup(TRUE.app_id([]))
        && egraph[t].nodes.iter().any(|f| f.head == FALSE)
    {
        to_explain.push((TRUE.app_empty(), FALSE.app_empty(), t));
    }

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

impl From<PRF> for CryptographicAssumption {
    /// Converts a `rules::PRF` into a `CryptographicAssumption::PRF`.
    fn from(v: PRF) -> Self {
        Self::PRF(v)
    }
}

impl Cryptography for PRF {
    fn ref_from_assumption(r: &CryptographicAssumption) -> Option<&Self> {
        match r {
            CryptographicAssumption::PRF(x) => Some(x),
            _ => None,
        }
    }

    fn name(&self) -> impl std::fmt::Display {
        format!("Pseudo-randomness of {}", self.hash)
    }

    fn register_nonce(
        &self,
        pbl: &mut ProblemState,
        variables: Vec<Variable>,
        n: Formula,
    ) -> anyhow::Result<()> {
        pbl.n_prf.register_nonce(variables, n);
        Ok(())
    }
}
