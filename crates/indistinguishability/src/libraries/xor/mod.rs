use egg::{Id, Pattern, Searcher, Subst};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain};
use static_init::dynamic;
use utils::ereturn_let;

use crate::libraries::fa::{self, FaElem, PATTERN_FA};
use crate::libraries::utils::Side;
use crate::problem::{PAnalysis, PRule, RcRule};
use crate::terms::{
    CryptographicAssumption, Cryptography, ETA, FRESH_NONCE, Function, LENGTH, NONCE, Rewrite,
    VAMPIRE,
};
use crate::{CVProgram, Lang, Problem, mk_signature, rexp};
declare_trace!($"enc");

mod vars {
    decl_vars!(pub const M:Bitstring, T, NT, P,
            A:Bitstring, B:Bitstring,
            PROOF: Bool, K:Nonce, K2:Nonce, N:Nonce, R:Nonce, H:Bool,
            SIDE:Any, U:Bitstring, V:Bitstring);
}

#[derive(Debug, Clone)]
pub struct XOr {
    #[allow(dead_code)]
    index: usize,
    xor: Function,
    xor_pattern: Pattern<Lang>,
}

decl_vars!(const NA:Bitstring, NB:Bitstring, X);

impl XOr {
    pub fn new_and_add(pbl: &mut Problem, index: usize, xor: Function) -> &Self {
        tr!("init xor: {xor}");
        assert_eq!(
            xor.signature,
            mk_signature!((Bitstring, Bitstring) -> Bitstring)
        );
        assert!(xor.cryptography.contains(&index));

        let xor = Self {
            index,
            xor: xor.clone(),

            xor_pattern: Pattern::from(&rexp!((xor #NA (NONCE #NB)))),
        };

        // declare prolog rules
        {
            let rules = chain![
                // search::mk_rules(pbl, &aenc),
                // subst::mk_rules(pbl, &aenc),
                // ind_cca::mk_rules(pbl, &aenc),
                // enc_kp::mk_rules(pbl, &aenc)
                [xor.clone().into_mrc()]
            ]
            .collect_vec();
            pbl.extra_rules_mut().extend(rules);
        }

        // declare rewrites
        {
            let rewrites = chain![xor.extra_rewrites(pbl)].collect_vec();
            pbl.extra_rewrite_mut().extend(rewrites);
        }

        xor.register_at(pbl, index).unwrap()
    }

    fn extra_rewrites(&self, _pbl: &Problem) -> impl Iterator<Item = Rewrite> {
        let Self { xor, .. } = self;
        // decl_vars!(a:Bitstring, b:Bitstring, c:Bitstring);
        // crate::mk_rewrite!()
        [
            mk_rewrite!(crate format!("{xor} symm"); (a Bitstring, b Bitstring) :
                (xor #a #b) => (xor #b #a)),
            mk_rewrite!(crate format!("{xor} assoc"); (a Bitstring, b Bitstring, c Bitstring):
                (xor #a (xor #b #c)) => (xor(xor #a #b) #c)),
            mk_rewrite!(crate format!("{xor} eq"); (a Bitstring, b Bitstring, c Bitstring) :
                (= #a (xor #b #c)) => (= (xor #b #a) #c)),
        ]
        .into_iter()
    }

    fn extract_xor_candidates<'pbl, 'a>(
        &self,
        egraph: &egg::EGraph<Lang, PAnalysis<'pbl>>,
        candidates2: &mut Vec<XorCandidate<'a>>,
        fas: &'a [FaElem],
        a: Id,
        idx: usize,
        side: Side,
        main_subst: &Subst,
    ) {
        if egraph[a]
            .nodes
            .iter()
            .any(|Lang { head, .. }| head == &self.xor)
        {
            candidates2.extend(
                self.xor_pattern
                    .search_eclass(egraph, a)
                    .into_iter()
                    .flat_map(|x| x.substs.into_iter())
                    .map(|s| {
                        let s = chain![s.iter(), main_subst.iter()]
                            .map(|(&v, i)| (v, i))
                            .collect();

                        XorCandidate {
                            fas,
                            idx,
                            subst: s,
                            side,
                        }
                    }),
            );
        }
    }
}

struct XorCandidate<'a> {
    fas: &'a [FaElem],
    idx: usize,
    subst: Subst,
    side: Side,
}

#[dynamic]
static PATTERN_CHECK_FRESH1: Pattern<Lang> = Pattern::from(&rexp!((FRESH_NONCE #NB #X true)));
#[dynamic]
static PATTERN_CHECK_FRESH2: Pattern<Lang> = Pattern::from(&rexp!((FRESH_NONCE #NB #NA true)));
#[dynamic]
static PATTERN_CHECK_LENGTH: Pattern<Lang> = Pattern::from(&rexp!((VAMPIRE (= (LENGTH #NA) ETA))));
#[dynamic]
static PATTERN_NEW: Pattern<Lang> = Pattern::from(&rexp!((NONCE #NB)));

impl<'pbl> Rule<Lang, PAnalysis<'pbl>, RcRule> for XOr {
    fn name(&self) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Borrowed("xor")
    }
    fn search(&self, prgm: &mut CVProgram<'pbl>, goal: egg::Id) -> Dependancy {
        ereturn_let!(let Some(substs) = PATTERN_FA.search_eclass(prgm.egraph(), goal), Dependancy::impossible());

        let candidates = fa::find_candidates(prgm, &substs);
        let egraph = prgm.egraph();

        let mut candidates2 = Vec::new();

        for (s, fas) in candidates.iter() {
            for (i, FaElem { a, b, .. }) in fas.iter().enumerate() {
                self.extract_xor_candidates(egraph, &mut candidates2, fas, *a, i, Side::Left, s);
                self.extract_xor_candidates(egraph, &mut candidates2, fas, *b, i, Side::Right, s);
            }
        }

        // let mut ret = Vec::with_capacity(candidates2.len());

        let egraph = prgm.egraph_mut();
        // for  in candidates2
        candidates2
            .into_iter()
            .map(
                |XorCandidate {
                     fas,
                     idx,
                     mut subst,
                     side,
                 }| {
                    let _id = fas[idx].get(side);

                    let faset = chain![
                        fas.iter()
                            .enumerate()
                            .filter_map(|(i, x)| (i != idx).then_some(*x)),
                        [fas[idx].set(side, PATTERN_NEW.apply_susbt(egraph, &subst))]
                    ]
                    .collect();
                    let (la, lb) = fa::create_lists(egraph, &fa::optimize_set(egraph, faset));

                    subst.insert(fa::A.as_egg(), la);
                    subst.insert(fa::B.as_egg(), lb);
                    let goal = PATTERN_FA.apply_susbt(egraph, &subst);

                    let checks = chain![
                        fas.iter().map(|f| f.get(side)),
                        [*subst.get(NA.as_egg()).unwrap()]
                    ]
                    .flat_map(|id| {
                        use std::ops::Deref;
                        subst.insert(X.as_egg(), id);
                        // PATTERN_CHECK_FRESH1.apply_susbt(egraph, &subst)
                        [
                            PATTERN_CHECK_FRESH1.deref(),
                            PATTERN_CHECK_FRESH2.deref(),
                            PATTERN_CHECK_LENGTH.deref(),
                        ]
                        .map(|p| p.apply_susbt(egraph, &subst))
                        .into_iter()
                    });

                    chain![checks, [goal]].collect_vec()
                },
            )
            .collect()

        // todo!()
    }
}

impl From<XOr> for CryptographicAssumption {
    fn from(v: XOr) -> Self {
        Self::XOr(v)
    }
}

impl Cryptography for XOr {
    fn ref_from_assumption(r: &CryptographicAssumption) -> Option<&Self> {
        match r {
            CryptographicAssumption::XOr(x) => Some(x),
            _ => None,
        }
    }

    fn name(&self) -> impl std::fmt::Display {
        &self.xor
    }
}
