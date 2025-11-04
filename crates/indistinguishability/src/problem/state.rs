use egg::Id;
use rustc_hash::FxHashSet;

#[derive(Debug, Clone, Default)]
pub struct ProblemState {
    /// already used nonces
    pub n_prf: FxHashSet<Id>,

    pub generated_ids: FxHashSet<Id>,
}

impl ProblemState {
    pub fn reset(&mut self) {
        *self = Default::default()
    }
}
