use itertools::{Itertools, chain};

use crate::problem::ProblemState;
use crate::terms::{
    CryptographicAssumption, Cryptography, Formula, Function, FunctionFlags, Rewrite, Sort,
    Variable,
};
use crate::{Problem, mk_signature};
declare_trace!($"enc");

mod vars {
    decl_vars!(pub const M:Bitstring, T, NT, P,
            A:Bitstring, B:Bitstring,
            PROOF: Bool, K:Nonce, K2:Nonce, N:Nonce, R:Nonce, H:Bool,
            SIDE:Any, U:Bitstring, V:Bitstring);
}

mod candidate;
mod enc_kp;
mod ind_cca;
mod search;
mod subst;

#[derive(Debug, Clone)]
pub struct AEnc {
    enc: Function,
    dec: Function,
    pk: Function,

    candidate_m: Function,
    candidate_b: Function,
    // search with no oracle
    // skip pk
    search_k_m: Function,
    search_k_b: Function,
    // search with decryption oracle
    search_o_m: Function,
    search_o_b: Function,

    search_k_trigger: Function,
    search_o_pre_trigger: Function,
    search_o_trigger: Function,

    subst: Function,

    index: usize,
}

#[derive(Debug, Clone)]
enum ProofHints {
    Keep,
    Replace,
    /// in `(fa_cons a b)`, keep `a` as is and propagate to `b`
    FaKeep(Function),
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

impl AEnc {
    pub fn new_and_add(
        pbl: &mut Problem,
        index: usize,
        enc: Function,
        dec: Function,
        pk: Function,
    ) -> &Self {
        tr!("init aenc: {enc}, {dec}, {pk}");
        assert_eq!(
            enc.signature,
            mk_signature!((Bitstring, Bitstring, Bitstring) -> Bitstring)
        );
        assert_eq!(
            dec.signature,
            mk_signature!((Bitstring, Bitstring) -> Bitstring)
        );
        assert_eq!(pk.signature, mk_signature!((Bitstring) -> Bitstring));

        let aenc = Self {
            enc: enc.clone(),
            dec,
            pk,
            // C[enc(m, nonce(r), pk(nonce(k)))], m, r, k
            candidate_m: declare!(pbl@index: format!("{enc}_candidate_m");
                Bitstring, Bitstring, Nonce, Nonce => Bitstring),
            candidate_b: declare!(pbl@index: format!("{enc}_candidate_b");
                Bool, Bitstring, Nonce, Nonce => Bool),

            // k ||> t | h
            search_k_m: declare!(pbl@index: format!("{enc}_search_k_m");
                Nonce, Bitstring, Bool => Bool),
            search_k_b: declare!(pbl@index: format!("{enc}_search_k_b");
                Nonce, Bool, Bool => Bool),
            // k, k', r, m ||> t  | h
            search_o_m: declare!(pbl@index: format!("{enc}_search_o_m");
                Nonce, Nonce, Nonce, Bitstring,
                    Bitstring, Bool => Bool),
            search_o_b: declare!(pbl@index: format!("{enc}_search_o_b");
                Nonce, Nonce, Nonce, Bitstring,
                    Bool, Bool => Bool),

            // k ||> frame@t p | h
            search_k_trigger: declare!(pbl@index: format!("{enc}_search_k_trigger");
                Nonce, Time, Protocol, Bool => Bool),
            // k, k', r ||> frame@t p  | h
            search_o_pre_trigger: declare!(pbl@index: format!("{enc}_search_o_pre_trigger");
                Nonce,Nonce,  Nonce, Time, Protocol, Bool => Bool),
            // k, r ||> frame@t p  | h
            search_o_trigger: declare!(pbl@index: format!("{enc}_search_o_trigger");
                Nonce, Nonce, Time, Protocol, Bool => Bool),
            // sid, u, v, _{_ -> nt @ proof}, b
            subst: declare!(pbl@index: format!("{enc}_search_o_b");
                Any, Bitstring, Bitstring,
                Bitstring, Bool,
                Bitstring => Bool),
            index,
        };

        // declare prolog rules
        {
            let rules = chain![
                search::mk_rules(pbl, &aenc),
                subst::mk_rules(pbl, &aenc),
                ind_cca::mk_rules(pbl, &aenc),
                enc_kp::mk_rules(pbl, &aenc)
            ]
            .collect_vec();
            pbl.extra_rules_mut().extend(rules);
        }

        // declare rewrites
        {
            let rewrites =
                chain![aenc.extra_rewrites(pbl), candidate::mk_rwrites(pbl, &aenc)].collect_vec();
            pbl.extra_rewrite_mut().extend(rewrites);
        }

        aenc.register_at(pbl, index).unwrap()
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
    pub fn get_search_k(&self, sort: Sort) -> Option<&Function> {
        match sort {
            Sort::Bitstring => Some(&self.search_k_m),
            Sort::Bool => Some(&self.search_k_b),
            _ => None,
        }
    }

    /// Returns the `search_o` function for a given output sort.
    pub fn get_search_o(&self, sort: Sort) -> Option<&Function> {
        match sort {
            Sort::Bitstring => Some(&self.search_o_m),
            Sort::Bool => Some(&self.search_o_b),
            _ => None,
        }
    }

    fn extra_rewrites(&self, _pbl: &Problem) -> impl Iterator<Item = Rewrite> {
        let Self { enc, dec, pk, .. } = self;
        // crate::mk_rewrite!()
        [mk_rewrite!(crate format!("{enc} simplification"); (m Bitstring, r Bitstring, k Bitstring):
            (dec (enc #m #r (pk #k)) #k) => (#m))
        ].into_iter()
    }
}

impl From<AEnc> for CryptographicAssumption {
    fn from(v: AEnc) -> Self {
        Self::AEnc(v)
    }
}

impl Cryptography for AEnc {
    fn ref_from_assumption(r: &CryptographicAssumption) -> Option<&Self> {
        match r {
            CryptographicAssumption::AEnc(r) => Some(r),
            _ => None,
        }
    }

    fn name(&self) -> impl std::fmt::Display {
        format!("Asymetric Encryption of {}", self.enc)
    }

    fn register_nonce(
        &self,
        pbl: &mut ProblemState,
        variables: Vec<Variable>,
        n: Formula,
    ) -> anyhow::Result<()> {
        pbl.n_enc_kp.register_nonce(variables, n);
        Ok(())
    }
}
