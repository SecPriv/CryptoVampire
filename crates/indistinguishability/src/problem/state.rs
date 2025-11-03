use egg::Id;

use crate::terms::Function;

#[derive(Debug, Clone, Default)]
pub struct ProblemState {
    /// already used nonces
    pub n_prf: Vec<Id>,
}

impl ProblemState {
    pub fn reset(&mut self) {
        *self = Default::default()
    }
}
