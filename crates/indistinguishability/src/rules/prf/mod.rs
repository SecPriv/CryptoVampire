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

impl PRF {
    pub fn new_and_add(pbl: &mut Problem, pos: usize, hash: Function) -> &Self {
        assert_eq!(
            hash.signature,
            mk_signature!((Bitstring, Bitstring) -> Bitstring)
        );
        assert!(hash.cryptography.contains(&pos));

        let candidate_bitstring = pbl
            .declare_function()
            .fresh_name("candidate_bitstring_prf")
            // h(m, k), m, k
            .inputs([Sort::Bitstring, Sort::Bitstring, Sort::Nonce])
            .output(Sort::Bool)
            .flags(FunctionFlags::PROLOG_ONLY)
            .cryptography([pos])
            .call();
        let candidate_bool = pbl
            .declare_function()
            .fresh_name("candidate_bool_prf")
            // h(m, k), m, k
            .inputs([Sort::Bool, Sort::Bitstring, Sort::Nonce])
            .output(Sort::Bool)
            .flags(FunctionFlags::PROLOG_ONLY)
            .cryptography([pos])
            .call();

        let search_bitstring = pbl
            .declare_function()
            .fresh_name("search_bitsring_prf")
            // m, k, x
            .inputs([Sort::Bitstring, Sort::Nonce, Sort::Bitstring])
            .output(Sort::Bool)
            .flags(FunctionFlags::PROLOG_ONLY)
            .cryptography([pos])
            .call();
        let search_bool = pbl
            .declare_function()
            .fresh_name("search_bool_prf")
            // m, k, x
            .inputs([Sort::Bitstring, Sort::Nonce, Sort::Bool])
            .output(Sort::Bool)
            .flags(FunctionFlags::PROLOG_ONLY)
            .cryptography([pos])
            .call();

        let search_trigger = pbl
            .declare_function()
            .fresh_name("prf_search_trigger")
            // m, k, ptcl, t
            .inputs([Sort::Bitstring, Sort::Nonce, Sort::Protocol, Sort::Time])
            .output(Sort::Bool)
            .flags(FunctionFlags::PROLOG_ONLY)
            .cryptography([pos])
            .call();

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
