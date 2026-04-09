use itertools::{Itertools, chain};

use super::{CryptographicAssumption, Cryptography};
use crate::libraries::Library;
use crate::libraries::utils::{RewriteSink, TwoSortFunction};
use crate::problem::ProblemState;
use crate::terms::{Formula, Function, FunctionFlags, Rewrite, Sort, Variable};
use crate::{Problem, mk_signature};
declare_trace!($"enc");

mod vars {
    decl_vars!(pub const M:Bitstring, T, NT, P:Protocol,
            A:Bitstring, B:Bitstring,
            A_N:Nonce, B_N:Nonce, A_B:Bool,
            PROOF: Bool, K:Nonce, K2:Nonce, N:Nonce, R:Nonce, H:Bool,
            SIDE:Any, U:Bitstring, V:Bitstring, C:MemoryCell);
}

mod candidate;
mod enc_kp;
mod ind_cca;
mod search;
mod subst;

/// When `enc` is IND-CCA1 and ENC-KP secure
#[derive(Debug, Clone)]
pub struct AEnc {
    pub enc: Function,
    pub dec: Function,
    pub pk: Option<Function>,

    /// `C[enc(m, nonce(r), pk(nonce(k)))], m, r, k`
    pub candidate: TwoSortFunction,

    /// search with no oracle skip `pk`.
    /// ```text
    /// k, k', r, m ||> t  | h
    ///
    /// Nonce, Nonce, Nonce, Bitstring  , _, Bool
    /// ```
    ///
    /// **!!!**: This is the search that finds instances.
    ///
    /// It does the search for both `k` and `k'`. In IND-CCA1 it is expected for
    /// `k` and `k'` to be the same
    pub search_k: TwoSortFunction,
    /// search with decryption oracle.
    /// ```text
    /// k ||> t  | h
    /// ```
    ///
    /// Conceptually these are computed before `C` so there cannot be instances
    /// within them. Notably, (see notes) we can split this search.
    pub search_o: TwoSortFunction,

    // triggers
    /// `k, k', r ||> frame@t p  | h`
    ///
    /// Pre triggers the search so we can do some processing on it (i.e., split
    /// the search easily)
    pub search_k_pre_trigger: Function,
    /// `k ||> frame@t p | h`
    ///
    /// Using the same trick as what we used for `search_o` we can search
    /// separatly
    pub search_k_trigger: Function,
    /// `k, r ||> frame@t p  | h`
    pub search_o_trigger: Function,
    /// `k, k', r ||> frame@t p | h` (for MACRO_MEMORY_CELL)
    pub search_k_trigger_mem: Function,
    /// `k ||> frame@t p | h` (for MACRO_MEMORY_CELL)
    pub search_o_trigger_mem: Function,
    /// `k, k', r ||> frame@t p | h` pre-trigger (for MACRO_MEMORY_CELL)
    pub search_k_pre_trigger_mem: Function,

    /// `sid, u, v, _{_ -> nt @ proof}, b`
    pub subst: Function,

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
        pk: Option<Function>,
    ) -> &Self {
        tr!("init aenc: {enc}, {dec}, {pk:?}");
        assert_eq!(
            enc.signature,
            mk_signature!((Bitstring, Bitstring, Bitstring) -> Bitstring)
        );
        assert_eq!(
            dec.signature,
            mk_signature!((Bitstring, Bitstring) -> Bitstring)
        );
        if let Some(pk) = &pk {
            assert_eq!(pk.signature, mk_signature!((Bitstring) -> Bitstring));
        }

        let aenc = Self {
            enc: enc.clone(),
            dec,
            pk,
            candidate: TwoSortFunction {
                m: declare!(pbl@index: format!("{enc}_candidate_m");
                Bitstring, Bitstring, Nonce, Nonce => Bitstring),
                b: declare!(pbl@index: format!("{enc}_candidate_b");
                Bool, Bitstring, Nonce, Nonce => Bool),
            },
            search_k: TwoSortFunction {
                m: declare!(pbl@index: format!("{enc}_search_k_m");
                Nonce, Nonce, Nonce, Bitstring,
                    Bitstring, Bool => Bool),
                b: declare!(pbl@index: format!("{enc}_search_k_b");
                Nonce, Nonce, Nonce, Bitstring,
                    Bool, Bool => Bool),
            },
            search_o: TwoSortFunction {
                m: declare!(pbl@index: format!("{enc}_search_o_m");
                Nonce, Bitstring, Bool => Bool),
                b: declare!(pbl@index: format!("{enc}_search_o_b");
                Nonce, Bool, Bool => Bool),
            },

            search_k_trigger: declare!(pbl@index: format!("{enc}_search_k_trigger");
                Nonce, Time, Protocol, Bool => Bool),
            search_k_pre_trigger: declare!(pbl@index: format!("{enc}_search_k_pre_trigger");
                Nonce, Nonce,  Nonce, Time, Protocol, Bool => Bool),
            search_k_trigger_mem: declare!(pbl@index: format!("{enc}_search_k_trigger_mem");
                Nonce, Time, Protocol, Bool, MemoryCell => Bool),
            search_k_pre_trigger_mem: declare!(pbl@index: format!("{enc}_search_k_pre_trigger_mem");
                Nonce, Nonce, Nonce, Time, Protocol, Bool, MemoryCell => Bool),

            search_o_trigger: declare!(pbl@index: format!("{enc}_search_o_trigger");
                Nonce, Time, Protocol, Bool => Bool),
            search_o_trigger_mem: declare!(pbl@index: format!("{enc}_search_o_trigger_mem");
                Nonce, Time, Protocol, Bool, MemoryCell => Bool),

            subst: declare!(pbl@index: format!("{enc}_search_o_b");
                Any, Bitstring, Bitstring,
                Bitstring, Bool,
                Bitstring => Bool),
            index,
        };

        // declare prolog rules
        {
            let mut sink = ::std::mem::take(pbl.extra_rules_mut());
            search::mk_rules(pbl, &aenc, &mut sink);
            subst::mk_rules(pbl, &aenc, &mut sink);
            ind_cca::mk_rules(pbl, &aenc, &mut sink);
            enc_kp::mk_rules(pbl, &aenc, &mut sink);

            *pbl.extra_rules_mut() = sink;
        }

        // declare rewrites
        {
            let mut sink = ::std::mem::take(pbl.extra_rewrite_mut());
            aenc.extra_rewrites(pbl, &mut sink);
            candidate::add_rwrites(pbl, &aenc, &mut sink);

            *pbl.extra_rewrite_mut() = sink;
        }

        aenc.register_at(pbl, index).unwrap()
    }

    fn extra_rewrites(&self, pbl: &Problem, sink: &mut impl RewriteSink) {
        let Self { enc, dec, pk, .. } = self;
        // crate::mk_rewrite!()
        if let Some(pk) = pk {
            sink.add_rewrite(pbl,
            mk_rewrite!{crate format!("{enc} simplification"); (m Bitstring, r Bitstring, k Bitstring):
                (dec (enc #m #r (pk #k)) #k) => (#m)}
        )
        } else {
            sink.add_rewrite(pbl,
                mk_rewrite!{crate format!("{enc} simplification"); (m Bitstring, r Bitstring, k Bitstring):
                (dec (enc #m #r #k) #k) => (#m)}
            )
        }
    }
}

impl From<AEnc> for CryptographicAssumption {
    fn from(v: AEnc) -> Self {
        Self::AEnc(v)
    }
}

impl Library for AEnc {}

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
