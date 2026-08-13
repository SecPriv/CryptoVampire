use super::*;
use crate::libraries::CryptographicAssumption;

impl Problem {
    pub fn default_cryptography() -> Vec<CryptographicAssumption> {
        vec![CryptographicAssumption::NoGuessingTh]
    }

    /// Returns the cryptographic assumptions
    pub fn cryptography(&self) -> &[CryptographicAssumption] {
        &self.cryptography
    }

    /// Returns a mutable reference to the cryptographic assumption at the given index
    pub fn cryptography_mut(&mut self, index: usize) -> Option<&mut CryptographicAssumption> {
        self.cryptography.get_mut(index)
    }

    /// Extends the cryptographic assumptions with `N` new default assumptions
    ///
    /// Returns an array of the indices of the new assumptions.
    pub fn extend_cryptography<const N: usize>(&mut self) -> [usize; N] {
        let ret = std::array::from_fn(|i| i + self.cryptography.len());
        self.cryptography.extend(ret.map(|_| Default::default()));
        ret
    }

    pub fn map_cryptography(&mut self, mut f: impl FnMut(&mut Self, &mut CryptographicAssumption)) {
        let mut crypto = ::std::mem::take(&mut self.cryptography);
        for c in &mut crypto {
            f(self, c)
        }
        self.cryptography = crypto;
    }
}
