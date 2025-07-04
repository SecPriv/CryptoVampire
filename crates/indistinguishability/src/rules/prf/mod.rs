use crate::{
    Problem, mk_signature,
    terms::{Function, FunctionFlags, Sort},
};

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
        };

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
}
