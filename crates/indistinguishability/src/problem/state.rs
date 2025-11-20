use egg::Id;
use rustc_hash::FxHashSet;

#[derive(Debug, Clone, Default)]
pub struct ProblemState {
    /// already used nonces
    pub n_prf: FxHashSet<Id>,
    pub n_enc_kp: FreshNonceSet,
    pub n_ddh: FreshNonceSet,

    pub generated_ids: FxHashSet<Id>,
}

impl ProblemState {
    pub fn reset(&mut self) {
        let Self { n_prf, n_enc_kp, n_ddh, generated_ids } = self;

        generated_ids.clear();
        n_prf.reset();
        n_enc_kp.reset();
        n_ddh.reset();

    }
}
