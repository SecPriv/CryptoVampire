use crate::{
    Problem, mk_signature,
    terms::{Function, FunctionFlags, Sort},
};

#[cfg(test)]
pub mod test;

#[derive(Debug)]
pub struct PRF {
    hash: Function,
    candidate: Function,
    search: Function,
}

impl PRF {
    pub fn new_and_add(pbl: &mut Problem, pos: usize, hash: Function) -> &Self {
        assert_eq!(
            hash.signature,
            mk_signature!((Bitstring, Bitstring) -> Bitstring)
        );
        assert!(hash.cryptography.contains(&pos));

        let candidate = pbl
            .declare_function()
            .fresh_name("candidate_prf")
            // h(m, k), m, k
            .inputs([Sort::Bitstring, Sort::Bitstring, Sort::Nonce])
            .output(Sort::Bool)
            .flags(FunctionFlags::PROLOG_ONLY)
            .cryptography([pos])
            .call();

        let search = pbl
            .declare_function()
            .fresh_name("search_prf")
            // m, k, x
            .inputs([Sort::Bitstring, Sort::Nonce, Sort::Bitstring])
            .output(Sort::Bool)
            .flags(FunctionFlags::PROLOG_ONLY)
            .cryptography([pos])
            .call();

        let prf = Self {
            hash,
            candidate,
            search,
        };

        let crypt_assumpt = pbl.cryptography_mut(pos).unwrap();
        assert!(crypt_assumpt.is_undefined());
        *crypt_assumpt = prf.into();
        crypt_assumpt.as_prf().unwrap()
    }
}
