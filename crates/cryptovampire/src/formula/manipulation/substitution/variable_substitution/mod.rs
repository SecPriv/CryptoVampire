mod one_var;
pub use one_var::{OneVarSubst, OneVarSubstF};

mod owned_var;
pub use owned_var::{MulitpleVarSubstF, MultipleVarSubst};

mod ref_substitution;
pub use ref_substitution::{FrozenMultipleVarSubst, FrozenOVSubstF, FrozenSubst, FrozenSubstF};
