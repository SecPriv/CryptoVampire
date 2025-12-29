use itertools::{Itertools, chain};

use crate::libraries::ddh::rule::DDHRule;
use crate::problem::{PRule, ProblemState};
use crate::terms::{
    CryptographicAssumption, Cryptography, Formula, Function, FunctionFlags, Rewrite, Sort,
    Variable,
};
use crate::{Problem, mk_signature};
declare_trace!($"enc");

#[allow(dead_code)]
mod vars {
    decl_vars!(pub const M:Bitstring, T, NT, P,
        NA: Nonce, NB:Nonce, NC:Nonce,
            A:Bitstring, B:Bitstring,
            TIME:Time, PTCL:Protocol,
            PROOF: Bool, K:Nonce, K2:Nonce, N:Nonce, R:Nonce, H:Bool,
            SIDE:Any, U:Bitstring, V:Bitstring);
}

mod candidate;
mod rule;
mod search;
mod subst;

#[derive(Debug, Clone)]
pub struct DDH {
    g: Function,
    exp: Function,

    candidate_m: Function,
    candidate_b: Function,
    // search with no oracle
    // skip pk
    search_m: Function,
    search_b: Function,

    search_trigger: Function,

    subst: Function,

    index: usize,
}

#[derive(Debug, Clone)]
enum ProofHints {
    Keep,
    Replace,
    /// beware of crypto functions
    Apply(Function),
}

macro_rules! declare {
    ($pbl:ident @ $pos:ident: $name:expr; $($s:expr),* => $o:ident) => {
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

impl DDH {
    pub fn new_and_add(pbl: &mut Problem, index: usize, g: Function, exp: Function) -> &Self {
        tr!("init ddh: {g}, {exp}");
        assert_eq!(g.signature, mk_signature!(() -> Bitstring));
        assert_eq!(
            exp.signature,
            mk_signature!((Bitstring, Bitstring) -> Bitstring)
        );

        let ddh = Self {
            g: g.clone(),
            exp,
            // C[(g^a)^b], a, b
            candidate_m: declare!(pbl@index: format!("ddh_{g}_candidate_m");
                Bitstring, Nonce, Nonce => Bitstring),
            candidate_b: declare!(pbl@index: format!("ddh_{g}_candidate_b");
                Bool, Nonce, Nonce => Bool),

            // a, b, c ||> t | h
            search_m: declare!(pbl@index: format!("ddh_{g}_search_m");
                Nonce, Nonce, Nonce, Bitstring, Bool => Bool),
            search_b: declare!(pbl@index: format!("ddh_{g}_search_b");
                Nonce, Nonce, Nonce, Bool, Bool => Bool),

            // a, b ||> frame@t p | h
            search_trigger: declare!(pbl@index: format!("ddh_{g}_search_trigger");
                Nonce, Nonce, Time, Protocol, Bool => Bool),
            // sid, u, v, _{_ -> nt @ proof}, b
            subst: declare!(pbl@index: format!("ddh_{g}_subst");
                Any, Bitstring, Bitstring,
                Bitstring, Bool,
                Bitstring => Bool),
            index,
        };

        // declare prolog rules
        {
            let rules = chain![
                search::mk_rules(pbl, &ddh),
                subst::mk_rules(pbl, &ddh),
                [DDHRule::new(&ddh).into_mrc()] /* ind_cca::mk_rules(pbl, &aenc),
                                                 * enc_kp::mk_rules(pbl, &aenc) */
            ]
            .collect_vec();
            pbl.extra_rules_mut().extend(rules);
        }

        // declare rewrites
        {
            let rewrites =
                chain![ddh.extra_rewrites(pbl), candidate::mk_rwrites(pbl, &ddh)].collect_vec();
            pbl.extra_rewrite_mut().extend(rewrites);
        }

        ddh.register_at(pbl, index).unwrap()
    }

    /// Returns the candidate function for a given output sort.
    pub fn get_candidate(&self, sort: Sort) -> Option<&Function> {
        match sort {
            Sort::Bitstring => Some(&self.candidate_m),
            Sort::Bool => Some(&self.candidate_b),
            _ => None,
        }
    }

    /// Returns the `search_k` function for a given output sort.
    pub fn get_search(&self, sort: Sort) -> Option<&Function> {
        match sort {
            Sort::Bitstring => Some(&self.search_m),
            Sort::Bool => Some(&self.search_b),
            _ => None,
        }
    }

    fn extra_rewrites(&self, _pbl: &Problem) -> impl Iterator<Item = Rewrite> {
        let Self {
            exp,
            search_m,
            search_b,
            search_trigger,
            ..
        } = self;
        [
            mk_rewrite!(crate format!("{exp} symm"); (x Bitstring, y Bitstring, z Bitstring):
                (exp (exp #x #y) #z) => (exp (exp #x #z) #y)),
            mk_rewrite!(crate prolog format!("{search_m} symm"); 
                (na Nonce, nb Nonce, nc Nonce, t Bitstring, h Bool):
                (search_m #na #nb #nc #t #h)
                    => (search_m #nb #na #nc #t #h)),
            mk_rewrite!(crate prolog format!("{search_b} symm"); 
                (na Nonce, nb Nonce, nc Nonce, t Bool, h Bool):
                (search_b #na #nb #nc #t #h)
                    => (search_b #nb #na #nc #t #h)),
            mk_rewrite!(crate prolog format!("{search_trigger} symm"); 
                (na Nonce, nb Nonce, t Time, p Protocol,  h Bool):
                (search_trigger #na #nb #t #p #h)
                    => (search_trigger #nb #na #t #p #h)),
        ]
        .into_iter()
    }
}

impl From<DDH> for CryptographicAssumption {
    fn from(v: DDH) -> Self {
        Self::DDH(v)
    }
}

impl Cryptography for DDH {
    fn ref_from_assumption(r: &CryptographicAssumption) -> Option<&Self> {
        match r {
            CryptographicAssumption::DDH(x) => Some(x),
            _ => None,
        }
    }

    fn name(&self) -> impl std::fmt::Display {
        format!("Decisional Diffie-Hellman hardness of {}", self.exp)
    }

    fn register_nonce(
        &self,
        pbl: &mut ProblemState,
        variables: Vec<Variable>,
        n: Formula,
    ) -> anyhow::Result<()> {
        pbl.n_ddh.register_nonce(variables, n);
        Ok(())
    }
}
